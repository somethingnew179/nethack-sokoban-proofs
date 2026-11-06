import NetHack.Soko22Hazard87.Compare146
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36750 (p : Pattern) (guard : d317756 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317755 p = 1 := by simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36749 p hg
    simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36751 (p : Pattern) (guard : d317757 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317752 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36746 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36752 (p : Pattern) (guard : d317758 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317757 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36751 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36753 (p : Pattern) (guard : d317759 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317758 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36752 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36754 (p : Pattern) (guard : d317760 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317759 p = 1 := by simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36753 p hg
    simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36755 (p : Pattern) (guard : d317761 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317756 p = 1 := by simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317760 p = 1 := by simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36754 p hg
    simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36756 (p : Pattern) (guard : d317762 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317761 p = 1 := by simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36755 p hg
    simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36757 (p : Pattern) (guard : d317763 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317762 p = 1 := by simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36756 p hg
    simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36758 (p : Pattern) (guard : d317764 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317763 p = 1 := by simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36757 p hg
    simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36759 (p : Pattern) (guard : d317765 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317764 p = 1 := by simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36758 p hg
    simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36760 (p : Pattern) (guard : d317766 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317766, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317766, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317765 p = 1 := by simpa only [d317766, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36759 p hg
    simpa only [d317766, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36761 (p : Pattern) (guard : d317767 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d317767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317766 p = 1 := by simpa only [d317767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36760 p hg
    simpa only [d317767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36762 (p : Pattern) (guard : d317768 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317767 p = 1 := by simpa only [d317768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36761 p hg
    simpa only [d317768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d317768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36763 (p : Pattern) (guard : d317737 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317737, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317737, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317736 p = 1 := by simpa only [d317737, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36730 p hg
    simpa only [d317737, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36764 (p : Pattern) (guard : d317742 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317742, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317742, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317741 p = 1 := by simpa only [d317742, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36735 p hg
    simpa only [d317742, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36765 (p : Pattern) (guard : d317743 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317737 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36763 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317742 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36764 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36766 (p : Pattern) (guard : d317744 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317742 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36764 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36767 (p : Pattern) (guard : d317745 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317743 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36765 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317744 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36766 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36768 (p : Pattern) (guard : d317746 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317745 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36767 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36769 (p : Pattern) (guard : d317747 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317746 p = 1 := by simpa only [d317747, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36768 p hg
    simpa only [d317747, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317747, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317747, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36770 (p : Pattern) (guard : d317748 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317748, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d317748, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317747 p = 1 := by simpa only [d317748, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36769 p hg
    simpa only [d317748, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36771 (p : Pattern) (guard : d317749 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317744 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36766 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36772 (p : Pattern) (guard : d317750 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317749 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36771 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36773 (p : Pattern) (guard : d317751 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317750 p = 1 := by simpa only [d317751, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36772 p hg
    simpa only [d317751, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317751, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317751, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36774 (p : Pattern) (guard : d317752 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317752, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d317752, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317751 p = 1 := by simpa only [d317752, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36773 p hg
    simpa only [d317752, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36775 (p : Pattern) (guard : d317753 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36770 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317752 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36774 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36776 (p : Pattern) (guard : d317754 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317753 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36775 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36777 (p : Pattern) (guard : d317755 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317754 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36776 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36778 (p : Pattern) (guard : d317756 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317755 p = 1 := by simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36777 p hg
    simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36779 (p : Pattern) (guard : d317757 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317752 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36774 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36780 (p : Pattern) (guard : d317758 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317757 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36779 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36781 (p : Pattern) (guard : d317759 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317758 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36780 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36782 (p : Pattern) (guard : d317760 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317759 p = 1 := by simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36781 p hg
    simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36783 (p : Pattern) (guard : d317761 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317756 p = 1 := by simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36778 p hg
    simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317760 p = 1 := by simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36784 (p : Pattern) (guard : d317762 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317761 p = 1 := by simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36783 p hg
    simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36785 (p : Pattern) (guard : d317763 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317762 p = 1 := by simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36784 p hg
    simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36786 (p : Pattern) (guard : d317764 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317763 p = 1 := by simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36785 p hg
    simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36787 (p : Pattern) (guard : d317765 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317764 p = 1 := by simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36786 p hg
    simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36788 (p : Pattern) (guard : d317769 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317755 p = 1 := by simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36749 p hg
    simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36789 (p : Pattern) (guard : d317770 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317759 p = 1 := by simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36753 p hg
    simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36790 (p : Pattern) (guard : d317771 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317769 p = 1 := by simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36788 p hg
    simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317770 p = 1 := by simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36789 p hg
    simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36791 (p : Pattern) (guard : d317772 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317771 p = 1 := by simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36790 p hg
    simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36792 (p : Pattern) (guard : d317773 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317772 p = 1 := by simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36791 p hg
    simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36793 (p : Pattern) (guard : d317774 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317773 p = 1 := by simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36792 p hg
    simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36794 (p : Pattern) (guard : d317775 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317774 p = 1 := by simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36793 p hg
    simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36795 (p : Pattern) (guard : d317776 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317765 p = 1 := by simpa only [d317776, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36787 p hg
    simpa only [d317776, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317775 p = 1 := by simpa only [d317776, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36794 p hg
    simpa only [d317776, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36796 (p : Pattern) (guard : d317777 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d317766 p = 1 := by simpa only [d317777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36760 p hg
    simpa only [d317777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317776 p = 1 := by simpa only [d317777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36795 p hg
    simpa only [d317777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36797 (p : Pattern) (guard : d317778 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317777 p = 1 := by simpa only [d317778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36796 p hg
    simpa only [d317778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d317778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36798 (p : Pattern) (guard : d317779 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317768 p = 1 := by simpa only [d317779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36762 p hg
    simpa only [d317779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317778 p = 1 := by simpa only [d317779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36797 p hg
    simpa only [d317779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36799 (p : Pattern) (guard : d317780 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317754 p = 1 := by simpa only [d317780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36748 p hg
    simpa only [d317780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36800 (p : Pattern) (guard : d317781 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317780 p = 1 := by simpa only [d317781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36799 p hg
    simpa only [d317781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36801 (p : Pattern) (guard : d317782 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317758 p = 1 := by simpa only [d317782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36752 p hg
    simpa only [d317782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36802 (p : Pattern) (guard : d317783 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317782 p = 1 := by simpa only [d317783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36801 p hg
    simpa only [d317783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36803 (p : Pattern) (guard : d317784 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317781 p = 1 := by simpa only [d317784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36800 p hg
    simpa only [d317784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317783 p = 1 := by simpa only [d317784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36802 p hg
    simpa only [d317784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36804 (p : Pattern) (guard : d317785 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317784 p = 1 := by simpa only [d317785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36803 p hg
    simpa only [d317785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36805 (p : Pattern) (guard : d317786 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317785 p = 1 := by simpa only [d317786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36804 p hg
    simpa only [d317786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36806 (p : Pattern) (guard : d317787 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317786 p = 1 := by simpa only [d317787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36805 p hg
    simpa only [d317787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36807 (p : Pattern) (guard : d317788 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317753 p = 1 := by simpa only [d317788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36747 p hg
    simpa only [d317788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36808 (p : Pattern) (guard : d317789 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317788 p = 1 := by simpa only [d317789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36807 p hg
    simpa only [d317789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36809 (p : Pattern) (guard : d317790 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317789 p = 1 := by simpa only [d317790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36808 p hg
    simpa only [d317790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36810 (p : Pattern) (guard : d317791 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317757 p = 1 := by simpa only [d317791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36751 p hg
    simpa only [d317791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36811 (p : Pattern) (guard : d317792 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317791 p = 1 := by simpa only [d317792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36810 p hg
    simpa only [d317792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36812 (p : Pattern) (guard : d317793 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317792 p = 1 := by simpa only [d317793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36811 p hg
    simpa only [d317793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36813 (p : Pattern) (guard : d317794 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317790 p = 1 := by simpa only [d317794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d317794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317793 p = 1 := by simpa only [d317794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36812 p hg
    simpa only [d317794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36814 (p : Pattern) (guard : d317795 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317794 p = 1 := by simpa only [d317795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36813 p hg
    simpa only [d317795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36815 (p : Pattern) (guard : d317796 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317795 p = 1 := by simpa only [d317796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36814 p hg
    simpa only [d317796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36816 (p : Pattern) (guard : d316858 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34357 p = 1 := by simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36173 p hg
    simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36817 (p : Pattern) (guard : d316859 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316858 p = 1 := by simpa only [d316859, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36816 p hg
    simpa only [d316859, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316859, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316859, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36818 (p : Pattern) (guard : d316860 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316859 p = 1 := by simpa only [d316860, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36817 p hg
    simpa only [d316860, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316860, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316860, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36819 (p : Pattern) (guard : d316861 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316861, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316861, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316860 p = 1 := by simpa only [d316861, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36818 p hg
    simpa only [d316861, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36820 (p : Pattern) (guard : d316862 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316861 p = 1 := by simpa only [d316862, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36819 p hg
    simpa only [d316862, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316862, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316862, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36821 (p : Pattern) (guard : d316863 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36173 p hg
    simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316590 p = 1 := by simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36195 p hg
    simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36822 (p : Pattern) (guard : d316864 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316863 p = 1 := by simpa only [d316864, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36821 p hg
    simpa only [d316864, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316864, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316864, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36823 (p : Pattern) (guard : d316865 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316864 p = 1 := by simpa only [d316865, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36822 p hg
    simpa only [d316865, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316865, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316865, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36824 (p : Pattern) (guard : d316866 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316866, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316866, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316865 p = 1 := by simpa only [d316866, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36823 p hg
    simpa only [d316866, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36825 (p : Pattern) (guard : d316867 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316866 p = 1 := by simpa only [d316867, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36824 p hg
    simpa only [d316867, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316867, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316867, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36826 (p : Pattern) (guard : d316868 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316862 p = 1 := by simpa only [d316868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36820 p hg
    simpa only [d316868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316867 p = 1 := by simpa only [d316868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36825 p hg
    simpa only [d316868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36827 (p : Pattern) (guard : d316869 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316590 p = 1 := by simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36195 p hg
    simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36828 (p : Pattern) (guard : d316870 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316869 p = 1 := by simpa only [d316870, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36827 p hg
    simpa only [d316870, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316870, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316870, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36829 (p : Pattern) (guard : d316871 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316870 p = 1 := by simpa only [d316871, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36828 p hg
    simpa only [d316871, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316871, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316871, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36830 (p : Pattern) (guard : d316872 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316872, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316872, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316871 p = 1 := by simpa only [d316872, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36829 p hg
    simpa only [d316872, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36831 (p : Pattern) (guard : d316873 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316872 p = 1 := by simpa only [d316873, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36830 p hg
    simpa only [d316873, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316873, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316873, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36832 (p : Pattern) (guard : d316874 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316873 p = 1 := by simpa only [d316874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36831 p hg
    simpa only [d316874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316788 p = 1 := by simpa only [d316874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36701 p hg
    simpa only [d316874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36833 (p : Pattern) (guard : d316875 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316868 p = 1 := by simpa only [d316875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36826 p hg
    simpa only [d316875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316874 p = 1 := by simpa only [d316875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36832 p hg
    simpa only [d316875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36834 (p : Pattern) (guard : d317797 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316875 p = 1 := by simpa only [d317797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36833 p hg
    simpa only [d317797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317718 p = 1 := by simpa only [d317797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36712 p hg
    simpa only [d317797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36835 (p : Pattern) (guard : d317798 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317798, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317798, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317797 p = 1 := by simpa only [d317798, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36834 p hg
    simpa only [d317798, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36836 (p : Pattern) (guard : d317799 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317799, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317799, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317798 p = 1 := by simpa only [d317799, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36835 p hg
    simpa only [d317799, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36837 (p : Pattern) (guard : d317800 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317717 p = 1 := by simpa only [d317800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36711 p hg
    simpa only [d317800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317733 p = 1 := by simpa only [d317800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36727 p hg
    simpa only [d317800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36838 (p : Pattern) (guard : d317801 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317718 p = 1 := by simpa only [d317801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36712 p hg
    simpa only [d317801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317800 p = 1 := by simpa only [d317801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36837 p hg
    simpa only [d317801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36839 (p : Pattern) (guard : d317802 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317802, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317802, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317801 p = 1 := by simpa only [d317802, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36838 p hg
    simpa only [d317802, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36840 (p : Pattern) (guard : d317803 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317803, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317803, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317802 p = 1 := by simpa only [d317803, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36839 p hg
    simpa only [d317803, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36841 (p : Pattern) (guard : d317804 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317799 p = 1 := by simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36836 p hg
    simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317803 p = 1 := by simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36840 p hg
    simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36842 (p : Pattern) (guard : d317805 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317804 p = 1 := by simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36841 p hg
    simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317743 p = 1 := by simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36737 p hg
    simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36843 (p : Pattern) (guard : d317806 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317805 p = 1 := by simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36842 p hg
    simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36844 (p : Pattern) (guard : d317807 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317806 p = 1 := by simpa only [d317807, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36843 p hg
    simpa only [d317807, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317807, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317807, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36845 (p : Pattern) (guard : d317808 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317808, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317808, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317807 p = 1 := by simpa only [d317808, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36844 p hg
    simpa only [d317808, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36846 (p : Pattern) (guard : d317809 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317808 p = 1 := by simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36845 p hg
    simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317748 p = 1 := by simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36742 p hg
    simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36847 (p : Pattern) (guard : d317810 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317809 p = 1 := by simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36846 p hg
    simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36848 (p : Pattern) (guard : d317811 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317810 p = 1 := by simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36847 p hg
    simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36849 (p : Pattern) (guard : d317812 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317811 p = 1 := by simpa only [d317812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36848 p hg
    simpa only [d317812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36850 (p : Pattern) (guard : d317813 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317812 p = 1 := by simpa only [d317813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36849 p hg
    simpa only [d317813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317756 p = 1 := by simpa only [d317813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d317813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36851 (p : Pattern) (guard : d317814 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317813 p = 1 := by simpa only [d317814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36850 p hg
    simpa only [d317814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36852 (p : Pattern) (guard : d317815 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36742 p hg
    simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36853 (p : Pattern) (guard : d317816 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317815 p = 1 := by simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36852 p hg
    simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36854 (p : Pattern) (guard : d317817 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317816 p = 1 := by simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36853 p hg
    simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36855 (p : Pattern) (guard : d317818 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317817 p = 1 := by simpa only [d317818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36854 p hg
    simpa only [d317818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36856 (p : Pattern) (guard : d317819 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317818 p = 1 := by simpa only [d317819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36855 p hg
    simpa only [d317819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36857 (p : Pattern) (guard : d317820 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317819 p = 1 := by simpa only [d317820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36856 p hg
    simpa only [d317820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36858 (p : Pattern) (guard : d317821 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317814 p = 1 := by simpa only [d317821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36851 p hg
    simpa only [d317821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317820 p = 1 := by simpa only [d317821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36857 p hg
    simpa only [d317821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36859 (p : Pattern) (guard : d317822 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d317796 p = 1 := by simpa only [d317822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36815 p hg
    simpa only [d317822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317821 p = 1 := by simpa only [d317822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36858 p hg
    simpa only [d317822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36860 (p : Pattern) (guard : d317823 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d317787 p = 1 := by simpa only [d317823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36806 p hg
    simpa only [d317823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317822 p = 1 := by simpa only [d317823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36859 p hg
    simpa only [d317823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36861 (p : Pattern) (guard : d317824 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317824, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317824, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317823 p = 1 := by simpa only [d317824, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36860 p hg
    simpa only [d317824, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36862 (p : Pattern) (guard : d317780 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317754 p = 1 := by simpa only [d317780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36776 p hg
    simpa only [d317780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36863 (p : Pattern) (guard : d317781 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317780 p = 1 := by simpa only [d317781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36862 p hg
    simpa only [d317781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36864 (p : Pattern) (guard : d317782 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317758 p = 1 := by simpa only [d317782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36780 p hg
    simpa only [d317782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36865 (p : Pattern) (guard : d317783 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317782 p = 1 := by simpa only [d317783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36864 p hg
    simpa only [d317783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36866 (p : Pattern) (guard : d317784 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317781 p = 1 := by simpa only [d317784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36863 p hg
    simpa only [d317784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317783 p = 1 := by simpa only [d317784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36865 p hg
    simpa only [d317784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36867 (p : Pattern) (guard : d317785 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317784 p = 1 := by simpa only [d317785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36866 p hg
    simpa only [d317785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36868 (p : Pattern) (guard : d317786 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317785 p = 1 := by simpa only [d317786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36867 p hg
    simpa only [d317786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36869 (p : Pattern) (guard : d317787 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317786 p = 1 := by simpa only [d317787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36868 p hg
    simpa only [d317787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36870 (p : Pattern) (guard : d317788 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317753 p = 1 := by simpa only [d317788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36775 p hg
    simpa only [d317788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36871 (p : Pattern) (guard : d317789 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317788 p = 1 := by simpa only [d317789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36870 p hg
    simpa only [d317789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36872 (p : Pattern) (guard : d317790 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317789 p = 1 := by simpa only [d317790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36871 p hg
    simpa only [d317790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36873 (p : Pattern) (guard : d317791 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317757 p = 1 := by simpa only [d317791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36779 p hg
    simpa only [d317791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36874 (p : Pattern) (guard : d317792 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317791 p = 1 := by simpa only [d317792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36873 p hg
    simpa only [d317792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36875 (p : Pattern) (guard : d317793 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317792 p = 1 := by simpa only [d317793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36874 p hg
    simpa only [d317793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36876 (p : Pattern) (guard : d317794 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317790 p = 1 := by simpa only [d317794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36872 p hg
    simpa only [d317794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317793 p = 1 := by simpa only [d317794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36875 p hg
    simpa only [d317794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36877 (p : Pattern) (guard : d317795 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317794 p = 1 := by simpa only [d317795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36876 p hg
    simpa only [d317795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36878 (p : Pattern) (guard : d317796 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317795 p = 1 := by simpa only [d317796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36877 p hg
    simpa only [d317796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36879 (p : Pattern) (guard : d317799 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317799, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317799, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317798 p = 1 := by simpa only [d317799, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36835 p hg
    simpa only [d317799, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36880 (p : Pattern) (guard : d317803 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317803, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317803, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317802 p = 1 := by simpa only [d317803, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36839 p hg
    simpa only [d317803, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36881 (p : Pattern) (guard : d317804 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317799 p = 1 := by simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36879 p hg
    simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317803 p = 1 := by simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36880 p hg
    simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36882 (p : Pattern) (guard : d317805 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317804 p = 1 := by simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36881 p hg
    simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317743 p = 1 := by simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36765 p hg
    simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36883 (p : Pattern) (guard : d317806 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317805 p = 1 := by simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36882 p hg
    simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36884 (p : Pattern) (guard : d317807 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317806 p = 1 := by simpa only [d317807, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36883 p hg
    simpa only [d317807, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317807, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317807, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36885 (p : Pattern) (guard : d317808 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317808, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d317808, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317807 p = 1 := by simpa only [d317808, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36884 p hg
    simpa only [d317808, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36886 (p : Pattern) (guard : d317809 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317808 p = 1 := by simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36885 p hg
    simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317748 p = 1 := by simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36770 p hg
    simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36887 (p : Pattern) (guard : d317810 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317809 p = 1 := by simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36886 p hg
    simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36888 (p : Pattern) (guard : d317811 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317810 p = 1 := by simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36887 p hg
    simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36889 (p : Pattern) (guard : d317812 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317811 p = 1 := by simpa only [d317812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36888 p hg
    simpa only [d317812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36890 (p : Pattern) (guard : d317813 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317812 p = 1 := by simpa only [d317813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36889 p hg
    simpa only [d317813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317756 p = 1 := by simpa only [d317813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36778 p hg
    simpa only [d317813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36891 (p : Pattern) (guard : d317814 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317813 p = 1 := by simpa only [d317814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36890 p hg
    simpa only [d317814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36892 (p : Pattern) (guard : d317815 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36770 p hg
    simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36893 (p : Pattern) (guard : d317816 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317815 p = 1 := by simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36892 p hg
    simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36894 (p : Pattern) (guard : d317817 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317816 p = 1 := by simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36893 p hg
    simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36895 (p : Pattern) (guard : d317818 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317817 p = 1 := by simpa only [d317818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36894 p hg
    simpa only [d317818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36896 (p : Pattern) (guard : d317819 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317818 p = 1 := by simpa only [d317819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36895 p hg
    simpa only [d317819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36897 (p : Pattern) (guard : d317820 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317819 p = 1 := by simpa only [d317820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36896 p hg
    simpa only [d317820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36898 (p : Pattern) (guard : d317821 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317814 p = 1 := by simpa only [d317821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36891 p hg
    simpa only [d317821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317820 p = 1 := by simpa only [d317821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36897 p hg
    simpa only [d317821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36899 (p : Pattern) (guard : d317822 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d317796 p = 1 := by simpa only [d317822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36878 p hg
    simpa only [d317822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317821 p = 1 := by simpa only [d317822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36898 p hg
    simpa only [d317822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36900 (p : Pattern) (guard : d317823 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d317787 p = 1 := by simpa only [d317823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36869 p hg
    simpa only [d317823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317822 p = 1 := by simpa only [d317823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36899 p hg
    simpa only [d317823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36901 (p : Pattern) (guard : d317825 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317780 p = 1 := by simpa only [d317825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36799 p hg
    simpa only [d317825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36902 (p : Pattern) (guard : d317826 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317782 p = 1 := by simpa only [d317826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36801 p hg
    simpa only [d317826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36903 (p : Pattern) (guard : d317827 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317825 p = 1 := by simpa only [d317827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36901 p hg
    simpa only [d317827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317826 p = 1 := by simpa only [d317827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36902 p hg
    simpa only [d317827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36904 (p : Pattern) (guard : d317828 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317827 p = 1 := by simpa only [d317828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36903 p hg
    simpa only [d317828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36905 (p : Pattern) (guard : d317829 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317828 p = 1 := by simpa only [d317829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36904 p hg
    simpa only [d317829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36906 (p : Pattern) (guard : d317830 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317829 p = 1 := by simpa only [d317830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36905 p hg
    simpa only [d317830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36907 (p : Pattern) (guard : d317831 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317789 p = 1 := by simpa only [d317831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36808 p hg
    simpa only [d317831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36908 (p : Pattern) (guard : d317832 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317792 p = 1 := by simpa only [d317832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36811 p hg
    simpa only [d317832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36909 (p : Pattern) (guard : d317833 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317831 p = 1 := by simpa only [d317833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36907 p hg
    simpa only [d317833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317832 p = 1 := by simpa only [d317833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36908 p hg
    simpa only [d317833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36910 (p : Pattern) (guard : d317834 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317833 p = 1 := by simpa only [d317834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36909 p hg
    simpa only [d317834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36911 (p : Pattern) (guard : d317835 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317834 p = 1 := by simpa only [d317835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36910 p hg
    simpa only [d317835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36912 (p : Pattern) (guard : d317836 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317811 p = 1 := by simpa only [d317836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36848 p hg
    simpa only [d317836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36913 (p : Pattern) (guard : d317837 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317836 p = 1 := by simpa only [d317837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36912 p hg
    simpa only [d317837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317769 p = 1 := by simpa only [d317837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36788 p hg
    simpa only [d317837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36914 (p : Pattern) (guard : d317838 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317837 p = 1 := by simpa only [d317838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36913 p hg
    simpa only [d317838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36915 (p : Pattern) (guard : d317839 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317817 p = 1 := by simpa only [d317839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36854 p hg
    simpa only [d317839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36916 (p : Pattern) (guard : d317840 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317839 p = 1 := by simpa only [d317840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36915 p hg
    simpa only [d317840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36917 (p : Pattern) (guard : d317841 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317840 p = 1 := by simpa only [d317841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36916 p hg
    simpa only [d317841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36918 (p : Pattern) (guard : d317842 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317838 p = 1 := by simpa only [d317842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36914 p hg
    simpa only [d317842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317841 p = 1 := by simpa only [d317842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36917 p hg
    simpa only [d317842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36919 (p : Pattern) (guard : d317843 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d317835 p = 1 := by simpa only [d317843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36911 p hg
    simpa only [d317843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317842 p = 1 := by simpa only [d317843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36918 p hg
    simpa only [d317843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36920 (p : Pattern) (guard : d317844 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d317830 p = 1 := by simpa only [d317844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36906 p hg
    simpa only [d317844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317843 p = 1 := by simpa only [d317844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36919 p hg
    simpa only [d317844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36921 (p : Pattern) (guard : d317845 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317823 p = 1 := by simpa only [d317845, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36900 p hg
    simpa only [d317845, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317844 p = 1 := by simpa only [d317845, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36920 p hg
    simpa only [d317845, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36922 (p : Pattern) (guard : d317846 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d317824 p = 1 := by simpa only [d317846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36861 p hg
    simpa only [d317846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317845 p = 1 := by simpa only [d317846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36921 p hg
    simpa only [d317846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36923 (p : Pattern) (guard : d317847 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317760 p = 1 := by simpa only [d317847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36754 p hg
    simpa only [d317847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36924 (p : Pattern) (guard : d317848 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317847 p = 1 := by simpa only [d317848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36923 p hg
    simpa only [d317848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36925 (p : Pattern) (guard : d317849 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317848 p = 1 := by simpa only [d317849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36924 p hg
    simpa only [d317849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36926 (p : Pattern) (guard : d317850 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317849 p = 1 := by simpa only [d317850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36925 p hg
    simpa only [d317850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36927 (p : Pattern) (guard : d317851 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317850 p = 1 := by simpa only [d317851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36926 p hg
    simpa only [d317851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36928 (p : Pattern) (guard : d317852 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317765 p = 1 := by simpa only [d317852, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36787 p hg
    simpa only [d317852, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317851 p = 1 := by simpa only [d317852, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36927 p hg
    simpa only [d317852, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36929 (p : Pattern) (guard : d317847 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317760 p = 1 := by simpa only [d317847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d317847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36930 (p : Pattern) (guard : d317848 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317847 p = 1 := by simpa only [d317848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36929 p hg
    simpa only [d317848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36931 (p : Pattern) (guard : d317849 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317848 p = 1 := by simpa only [d317849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36930 p hg
    simpa only [d317849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36932 (p : Pattern) (guard : d317850 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317849 p = 1 := by simpa only [d317850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36931 p hg
    simpa only [d317850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36933 (p : Pattern) (guard : d317851 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317850 p = 1 := by simpa only [d317851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36932 p hg
    simpa only [d317851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36934 (p : Pattern) (guard : d317853 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317770 p = 1 := by simpa only [d317853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36789 p hg
    simpa only [d317853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36935 (p : Pattern) (guard : d317854 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317853 p = 1 := by simpa only [d317854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36934 p hg
    simpa only [d317854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36936 (p : Pattern) (guard : d317855 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317854 p = 1 := by simpa only [d317855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36935 p hg
    simpa only [d317855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36937 (p : Pattern) (guard : d317856 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317855 p = 1 := by simpa only [d317856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36936 p hg
    simpa only [d317856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36938 (p : Pattern) (guard : d317857 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317856 p = 1 := by simpa only [d317857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36937 p hg
    simpa only [d317857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36939 (p : Pattern) (guard : d317858 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317851 p = 1 := by simpa only [d317858, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36933 p hg
    simpa only [d317858, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317857 p = 1 := by simpa only [d317858, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36938 p hg
    simpa only [d317858, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36940 (p : Pattern) (guard : d317859 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d317852 p = 1 := by simpa only [d317859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36928 p hg
    simpa only [d317859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317858 p = 1 := by simpa only [d317859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36939 p hg
    simpa only [d317859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36941 (p : Pattern) (guard : d317860 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317846 p = 1 := by simpa only [d317860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36922 p hg
    simpa only [d317860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317859 p = 1 := by simpa only [d317860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36940 p hg
    simpa only [d317860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36942 (p : Pattern) (guard : d317861 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317860 p = 1 := by simpa only [d317861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36941 p hg
    simpa only [d317861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d317861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36943 (p : Pattern) (guard : d317862 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d317779 p = 1 := by simpa only [d317862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36798 p hg
    simpa only [d317862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317861 p = 1 := by simpa only [d317862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36942 p hg
    simpa only [d317862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36944 (p : Pattern) (guard : d316858 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34357 p = 1 := by simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36315 p hg
    simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36945 (p : Pattern) (guard : d316859 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316858 p = 1 := by simpa only [d316859, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36944 p hg
    simpa only [d316859, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316859, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316859, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36946 (p : Pattern) (guard : d316860 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316859 p = 1 := by simpa only [d316860, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36945 p hg
    simpa only [d316860, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316860, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316860, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36947 (p : Pattern) (guard : d316861 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316861, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316861, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316860 p = 1 := by simpa only [d316861, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36946 p hg
    simpa only [d316861, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36948 (p : Pattern) (guard : d316862 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316861 p = 1 := by simpa only [d316862, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36947 p hg
    simpa only [d316862, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316862, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316862, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36949 (p : Pattern) (guard : d316863 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36315 p hg
    simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316590 p = 1 := by simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36337 p hg
    simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36950 (p : Pattern) (guard : d316864 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316863 p = 1 := by simpa only [d316864, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36949 p hg
    simpa only [d316864, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316864, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316864, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36951 (p : Pattern) (guard : d316865 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316864 p = 1 := by simpa only [d316865, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36950 p hg
    simpa only [d316865, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316865, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316865, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36952 (p : Pattern) (guard : d316866 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316866, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316866, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316865 p = 1 := by simpa only [d316866, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36951 p hg
    simpa only [d316866, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36953 (p : Pattern) (guard : d316867 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316866 p = 1 := by simpa only [d316867, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36952 p hg
    simpa only [d316867, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316867, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316867, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36954 (p : Pattern) (guard : d316868 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316862 p = 1 := by simpa only [d316868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36948 p hg
    simpa only [d316868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316867 p = 1 := by simpa only [d316868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36953 p hg
    simpa only [d316868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36955 (p : Pattern) (guard : d316869 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316590 p = 1 := by simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36337 p hg
    simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36956 (p : Pattern) (guard : d316870 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316869 p = 1 := by simpa only [d316870, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36955 p hg
    simpa only [d316870, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316870, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316870, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36957 (p : Pattern) (guard : d316871 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316870 p = 1 := by simpa only [d316871, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36956 p hg
    simpa only [d316871, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316871, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316871, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36958 (p : Pattern) (guard : d316872 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316872, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316872, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316871 p = 1 := by simpa only [d316872, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36957 p hg
    simpa only [d316872, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36959 (p : Pattern) (guard : d316873 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316872 p = 1 := by simpa only [d316873, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36958 p hg
    simpa only [d316873, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316873, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316873, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36960 (p : Pattern) (guard : d1531 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare36961 (p : Pattern) (guard : d1547 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36960 p hg
    simpa only [d1547, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d1547, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36962 (p : Pattern) (guard : d39244 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36961 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36963 (p : Pattern) (guard : d258107 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36962 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36964 (p : Pattern) (guard : d258108 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36963 p hg
    simpa only [d258108, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d258108, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36965 (p : Pattern) (guard : d316775 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36325 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36964 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36966 (p : Pattern) (guard : d316776 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316775 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36965 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36967 (p : Pattern) (guard : d316777 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316776 p = 1 := by simpa only [d316777, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36966 p hg
    simpa only [d316777, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316777, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d316777, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36968 (p : Pattern) (guard : d316784 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36337 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36967 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36969 (p : Pattern) (guard : d316785 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316784 p = 1 := by simpa only [d316785, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36968 p hg
    simpa only [d316785, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316785, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316785, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36970 (p : Pattern) (guard : d316786 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316785 p = 1 := by simpa only [d316786, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36969 p hg
    simpa only [d316786, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316786, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316786, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36971 (p : Pattern) (guard : d316787 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316787, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316787, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316786 p = 1 := by simpa only [d316787, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36970 p hg
    simpa only [d316787, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36972 (p : Pattern) (guard : d316788 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316787 p = 1 := by simpa only [d316788, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36971 p hg
    simpa only [d316788, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316788, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316788, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36973 (p : Pattern) (guard : d316874 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316873 p = 1 := by simpa only [d316874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36959 p hg
    simpa only [d316874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316788 p = 1 := by simpa only [d316874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36972 p hg
    simpa only [d316874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36974 (p : Pattern) (guard : d316875 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316868 p = 1 := by simpa only [d316875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36954 p hg
    simpa only [d316875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316874 p = 1 := by simpa only [d316875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36973 p hg
    simpa only [d316875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36975 (p : Pattern) (guard : d40834 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare36976 (p : Pattern) (guard : d317691 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40834 p = 1 := by simpa only [d317691, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36975 p hg
    simpa only [d317691, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317691, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d317691, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36977 (p : Pattern) (guard : d317692 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317691 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36976 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36978 (p : Pattern) (guard : d317693 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317692 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36977 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36979 (p : Pattern) (guard : d317694 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317693 p = 1 := by simpa only [d317694, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36978 p hg
    simpa only [d317694, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317694, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d317694, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36980 (p : Pattern) (guard : d317695 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317694 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36979 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36981 (p : Pattern) (guard : d316767 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35813 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36964 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36982 (p : Pattern) (guard : d317696 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317695 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36980 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316767 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36981 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36983 (p : Pattern) (guard : d317697 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317696 p = 1 := by simpa only [d317697, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36982 p hg
    simpa only [d317697, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317697, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d317697, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36984 (p : Pattern) (guard : d317698 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36315 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317697 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36985 (p : Pattern) (guard : d317699 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317698 p = 1 := by simpa only [d317699, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36984 p hg
    simpa only [d317699, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317699, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317699, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36986 (p : Pattern) (guard : d317700 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317699 p = 1 := by simpa only [d317700, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36985 p hg
    simpa only [d317700, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317700, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317700, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36987 (p : Pattern) (guard : d317701 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317701, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317701, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317700 p = 1 := by simpa only [d317701, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36986 p hg
    simpa only [d317701, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36988 (p : Pattern) (guard : d317702 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317701 p = 1 := by simpa only [d317702, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36987 p hg
    simpa only [d317702, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317702, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317702, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36989 (p : Pattern) (guard : d317703 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36967 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36990 (p : Pattern) (guard : d317704 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317703 p = 1 := by simpa only [d317704, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36989 p hg
    simpa only [d317704, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317704, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317704, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36991 (p : Pattern) (guard : d317705 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317704 p = 1 := by simpa only [d317705, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36990 p hg
    simpa only [d317705, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317705, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317705, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36992 (p : Pattern) (guard : d317706 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317706, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317706, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317705 p = 1 := by simpa only [d317706, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36991 p hg
    simpa only [d317706, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36993 (p : Pattern) (guard : d317707 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317706 p = 1 := by simpa only [d317707, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36992 p hg
    simpa only [d317707, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317707, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317707, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36994 (p : Pattern) (guard : d317708 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317702 p = 1 := by simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36988 p hg
    simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317707 p = 1 := by simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36993 p hg
    simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36995 (p : Pattern) (guard : d317709 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36979 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36964 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36996 (p : Pattern) (guard : d258109 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36964 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36997 (p : Pattern) (guard : d317710 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317709 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36995 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36996 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36998 (p : Pattern) (guard : d317711 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317710 p = 1 := by simpa only [d317711, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36997 p hg
    simpa only [d317711, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317711, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d317711, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36999 (p : Pattern) (guard : d317712 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317711 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36998 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
