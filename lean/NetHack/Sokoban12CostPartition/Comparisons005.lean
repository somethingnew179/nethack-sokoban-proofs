/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare700 (p : Pattern) (guard : d819 p = 1) : d113 p ≤ (0 : Int) + d227 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d819, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d819, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d819, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d819, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare701 (p : Pattern) (guard : d820 p = 1) : d210 p ≤ (0 : Int) + d366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d820, d210, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare700 p hg
    simpa only [d820, d210, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d820, d210, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare190 p hg
    simpa only [d820, d210, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare702 (p : Pattern) (guard : d758 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare703 (p : Pattern) (guard : d758 p = 1) : d68 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare702 p hg
    simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare704 (p : Pattern) (guard : d758 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare705 (p : Pattern) (guard : d758 p = 1) : d69 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare704 p hg
    simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare706 (p : Pattern) (guard : d758 p = 1) : d70 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare703 p hg
    simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare705 p hg
    simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare707 (p : Pattern) (guard : d818 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare708 (p : Pattern) (guard : d818 p = 1) : d211 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d211, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d211, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d211, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d211, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare709 (p : Pattern) (guard : d818 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare710 (p : Pattern) (guard : d818 p = 1) : d212 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d212, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d212, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d212, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d212, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare711 (p : Pattern) (guard : d818 p = 1) : d213 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d213, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare708 p hg
    simpa only [d213, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d213, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d213, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare712 (p : Pattern) (guard : d819 p = 1) : d214 p ≤ (0 : Int) + d231 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d819, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d819, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d819, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d819, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare713 (p : Pattern) (guard : d820 p = 1) : d215 p ≤ (0 : Int) + d367 p := by
  cases selected : p 133 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d820, d215, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d820, d215, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d820, d215, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d820, d215, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare714 (p : Pattern) (guard : d820 p = 1) : d216 p ≤ (0 : Int) + d368 p := by
  cases selected : p 132 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d216, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare701 p hg
    simpa only [d216, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d216, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare713 p hg
    simpa only [d216, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare715 (p : Pattern) (guard : d818 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare716 (p : Pattern) (guard : d819 p = 1) : d67 p ≤ (0 : Int) + d369 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d819, d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d819, d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d819, d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d819, d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare717 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare718 (p : Pattern) (guard : d820 p = 1) : d217 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d820, d217, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare716 p hg
    simpa only [d820, d217, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d820, d217, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare717 p hg
    simpa only [d820, d217, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare719 (p : Pattern) (guard : d819 p = 1) : d71 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d819, d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d819, d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d819, d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d819, d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare720 (p : Pattern) (guard : d820 p = 1) : d73 p ≤ (0 : Int) + d372 p := by
  cases selected : p 133 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d820, d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare719 p hg
    simpa only [d820, d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d820, d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d820, d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare721 (p : Pattern) (guard : d820 p = 1) : d218 p ≤ (0 : Int) + d373 p := by
  cases selected : p 132 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d218, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare718 p hg
    simpa only [d218, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d218, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare720 p hg
    simpa only [d218, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare722 (p : Pattern) (guard : d820 p = 1) : d219 p ≤ (0 : Int) + d374 p := by
  cases selected : p 108 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d219, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d219, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d219, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare721 p hg
    simpa only [d219, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare723 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d242 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare724 (p : Pattern) (guard : d821 p = 1) : d210 p ≤ (0 : Int) + d315 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d821, d210, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare331 p hg
    simpa only [d821, d210, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d821, d210, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare723 p hg
    simpa only [d821, d210, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare725 (p : Pattern) (guard : d798 p = 1) : d70 p ≤ (0 : Int) + d70 p := by
  omega
theorem compare726 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare727 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d107, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d794, d107, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d107, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare726 p hg
    simpa only [d794, d107, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare728 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare729 (p : Pattern) (guard : d798 p = 1) : d211 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d798, d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare730 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare731 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d110, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d794, d110, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d110, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare730 p hg
    simpa only [d794, d110, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare732 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare733 (p : Pattern) (guard : d798 p = 1) : d212 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare731 p hg
    simpa only [d798, d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare734 (p : Pattern) (guard : d798 p = 1) : d213 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare729 p hg
    simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare733 p hg
    simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare735 (p : Pattern) (guard : d798 p = 1) : d214 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d214, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare725 p hg
    simpa only [d214, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d214, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d214, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare736 (p : Pattern) (guard : d824 p = 1) : d215 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d824, d215, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d824, d215, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d824, d215, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d824, d215, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare737 (p : Pattern) (guard : d825 p = 1) : d216 p ≤ (0 : Int) + d316 p := by
  cases selected : p 132 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d825, d216, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare724 p hg
    simpa only [d825, d216, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d824 p = 1 := by simpa only [d825, d216, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare736 p hg
    simpa only [d825, d216, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare738 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare739 (p : Pattern) (guard : d821 p = 1) : d217 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d821, d217, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare349 p hg
    simpa only [d821, d217, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d821, d217, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare738 p hg
    simpa only [d821, d217, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare740 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare741 (p : Pattern) (guard : d794 p = 1) : d57 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare740 p hg
    simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare742 (p : Pattern) (guard : d798 p = 1) : d68 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d68, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare741 p hg
    simpa only [d798, d68, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d68, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d68, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare743 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare744 (p : Pattern) (guard : d794 p = 1) : d63 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare743 p hg
    simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare745 (p : Pattern) (guard : d798 p = 1) : d69 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d69, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare744 p hg
    simpa only [d798, d69, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d69, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d69, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare746 (p : Pattern) (guard : d798 p = 1) : d70 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d70, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare742 p hg
    simpa only [d70, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d70, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d70, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare747 (p : Pattern) (guard : d798 p = 1) : d71 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d71, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare746 p hg
    simpa only [d71, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d71, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d71, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare748 (p : Pattern) (guard : d824 p = 1) : d73 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d824, d73, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare747 p hg
    simpa only [d824, d73, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d824, d73, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d824, d73, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare749 (p : Pattern) (guard : d825 p = 1) : d218 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d825, d218, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare739 p hg
    simpa only [d825, d218, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d824 p = 1 := by simpa only [d825, d218, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare748 p hg
    simpa only [d825, d218, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare750 (p : Pattern) (guard : d825 p = 1) : d219 p ≤ (0 : Int) + d319 p := by
  cases selected : p 108 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d219, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare737 p hg
    simpa only [d219, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d219, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare749 p hg
    simpa only [d219, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare751 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare752 (p : Pattern) (guard : d755 p = 1) : d74 p ≤ (0 : Int) + d75 p := by
  cases selected : p 108 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d755, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d755, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d755, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare751 p hg
    simpa only [d755, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare753 (p : Pattern) (guard : d738 p = 1) : d74 p ≤ (0 : Int) + d74 p := by
  omega
theorem compare754 (p : Pattern) (guard : d826 p = 1) : d67 p ≤ (0 : Int) + d227 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d826, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d826, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d826, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare187 p hg
    simpa only [d826, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare755 (p : Pattern) (guard : d826 p = 1) : d71 p ≤ (0 : Int) + d231 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d826, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d826, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d826, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare190 p hg
    simpa only [d826, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare756 (p : Pattern) (guard : d826 p = 1) : d72 p ≤ (0 : Int) + d366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d72, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare754 p hg
    simpa only [d72, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d72, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare755 p hg
    simpa only [d72, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare757 (p : Pattern) (guard : d826 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare758 (p : Pattern) (guard : d826 p = 1) : d73 p ≤ (0 : Int) + d367 p := by
  cases selected : p 133 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d73, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare755 p hg
    simpa only [d73, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d73, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare757 p hg
    simpa only [d73, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare759 (p : Pattern) (guard : d826 p = 1) : d74 p ≤ (0 : Int) + d368 p := by
  cases selected : p 132 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d74, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare756 p hg
    simpa only [d74, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d74, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare758 p hg
    simpa only [d74, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare760 (p : Pattern) (guard : d826 p = 1) : d67 p ≤ (0 : Int) + d369 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d826, d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d826, d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d826, d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d826, d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare761 (p : Pattern) (guard : d826 p = 1) : d71 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d826, d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d826, d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d826, d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d826, d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare762 (p : Pattern) (guard : d826 p = 1) : d72 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d72, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare760 p hg
    simpa only [d72, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d72, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare761 p hg
    simpa only [d72, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare763 (p : Pattern) (guard : d826 p = 1) : d73 p ≤ (0 : Int) + d372 p := by
  cases selected : p 133 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare761 p hg
    simpa only [d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare757 p hg
    simpa only [d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare764 (p : Pattern) (guard : d826 p = 1) : d74 p ≤ (0 : Int) + d373 p := by
  cases selected : p 132 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d74, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare762 p hg
    simpa only [d74, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d74, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare763 p hg
    simpa only [d74, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare765 (p : Pattern) (guard : d826 p = 1) : d74 p ≤ (0 : Int) + d374 p := by
  cases selected : p 108 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare759 p hg
    simpa only [d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare764 p hg
    simpa only [d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare766 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare767 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare768 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (2 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare767 p hg
    simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare769 (p : Pattern) (guard : d830 p = 1) : d57 p ≤ (2 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare766 p hg
    simpa only [d830, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d830, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare770 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare771 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare772 (p : Pattern) (guard : d829 p = 1) : d61 p ≤ (2 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare771 p hg
    simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare773 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare772 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare774 (p : Pattern) (guard : d830 p = 1) : d63 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare770 p hg
    simpa only [d830, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare773 p hg
    simpa only [d830, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare775 (p : Pattern) (guard : d830 p = 1) : d64 p ≤ (2 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare769 p hg
    simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare774 p hg
    simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare776 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare777 (p : Pattern) (guard : d831 p = 1) : d67 p ≤ (2 : Int) + d13 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare775 p hg
    simpa only [d831, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare776 p hg
    simpa only [d831, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare778 (p : Pattern) (guard : d830 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare779 (p : Pattern) (guard : d830 p = 1) : d68 p ≤ (2 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare769 p hg
    simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare780 (p : Pattern) (guard : d830 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare781 (p : Pattern) (guard : d830 p = 1) : d69 p ≤ (2 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare774 p hg
    simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare780 p hg
    simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare782 (p : Pattern) (guard : d830 p = 1) : d70 p ≤ (2 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare779 p hg
    simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare783 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d834 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare784 (p : Pattern) (guard : d831 p = 1) : d71 p ≤ (2 : Int) + d834 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare782 p hg
    simpa only [d831, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare783 p hg
    simpa only [d831, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare785 (p : Pattern) (guard : d831 p = 1) : d72 p ≤ (2 : Int) + d835 p := by
  cases selected : p 133 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d72, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d72, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d72, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare784 p hg
    simpa only [d72, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare786 (p : Pattern) (guard : d831 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare787 (p : Pattern) (guard : d831 p = 1) : d73 p ≤ (2 : Int) + d836 p := by
  cases selected : p 133 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d73, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare784 p hg
    simpa only [d73, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d73, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare786 p hg
    simpa only [d73, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare788 (p : Pattern) (guard : d831 p = 1) : d74 p ≤ (2 : Int) + d837 p := by
  cases selected : p 132 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d74, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare785 p hg
    simpa only [d74, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d74, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d74, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare789 (p : Pattern) (guard : d831 p = 1) : d67 p ≤ (2 : Int) + d838 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d67, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare775 p hg
    simpa only [d831, d67, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d67, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d831, d67, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare790 (p : Pattern) (guard : d831 p = 1) : d71 p ≤ (2 : Int) + d839 p := by
  cases selected : p 134 with
  | false =>
    have hg : d830 p = 1 := by simpa only [d831, d71, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare782 p hg
    simpa only [d831, d71, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d831, d71, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d831, d71, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare791 (p : Pattern) (guard : d831 p = 1) : d72 p ≤ (2 : Int) + d840 p := by
  cases selected : p 133 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d72, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d72, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d72, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare790 p hg
    simpa only [d72, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare792 (p : Pattern) (guard : d831 p = 1) : d73 p ≤ (2 : Int) + d841 p := by
  cases selected : p 133 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d73, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare790 p hg
    simpa only [d73, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d73, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare786 p hg
    simpa only [d73, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare793 (p : Pattern) (guard : d831 p = 1) : d74 p ≤ (2 : Int) + d842 p := by
  cases selected : p 132 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d74, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d74, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d74, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare792 p hg
    simpa only [d74, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare794 (p : Pattern) (guard : d831 p = 1) : d74 p ≤ (2 : Int) + d843 p := by
  cases selected : p 108 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare788 p hg
    simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d831 p = 1 := by simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare793 p hg
    simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare795 (p : Pattern) (guard : d737 p = 1) : d74 p ≤ (0 : Int) + d236 p := by
  cases selected : p 108 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare195 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare796 (p : Pattern) (guard : d765 p = 1) : d72 p ≤ (0 : Int) + d217 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d765, d72, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare568 p hg
    simpa only [d765, d72, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d765, d72, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d765, d72, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare797 (p : Pattern) (guard : d765 p = 1) : d74 p ≤ (0 : Int) + d218 p := by
  cases selected : p 132 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d74, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d74, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d74, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare570 p hg
    simpa only [d74, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare798 (p : Pattern) (guard : d765 p = 1) : d74 p ≤ (0 : Int) + d219 p := by
  cases selected : p 108 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare205 p hg
    simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare797 p hg
    simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare799 (p : Pattern) (guard : d0 p = 1) : d67 p ≤ (2 : Int) + d214 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare800 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (2 : Int) + d70 p := by
  omega
theorem compare801 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare802 (p : Pattern) (guard : d737 p = 1) : d71 p ≤ (2 : Int) + d214 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d71, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare800 p hg
    simpa only [d737, d71, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d71, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare801 p hg
    simpa only [d737, d71, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare803 (p : Pattern) (guard : d789 p = 1) : d72 p ≤ (2 : Int) + d214 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d789, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare799 p hg
    simpa only [d789, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d789, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare802 p hg
    simpa only [d789, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare804 (p : Pattern) (guard : d0 p = 1) : d73 p ≤ (2 : Int) + d214 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare805 (p : Pattern) (guard : d790 p = 1) : d74 p ≤ (2 : Int) + d214 p := by
  cases selected : p 132 with
  | false =>
    have hg : d789 p = 1 := by simpa only [d790, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare803 p hg
    simpa only [d790, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d790, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare804 p hg
    simpa only [d790, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare806 (p : Pattern) (guard : d0 p = 1) : d67 p ≤ (2 : Int) + d71 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare807 (p : Pattern) (guard : d737 p = 1) : d71 p ≤ (2 : Int) + d71 p := by
  omega
theorem compare808 (p : Pattern) (guard : d789 p = 1) : d72 p ≤ (2 : Int) + d71 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d789, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare806 p hg
    simpa only [d789, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d789, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare807 p hg
    simpa only [d789, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare809 (p : Pattern) (guard : d0 p = 1) : d73 p ≤ (2 : Int) + d71 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare810 (p : Pattern) (guard : d790 p = 1) : d74 p ≤ (2 : Int) + d71 p := by
  cases selected : p 132 with
  | false =>
    have hg : d789 p = 1 := by simpa only [d790, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare808 p hg
    simpa only [d790, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d790, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare809 p hg
    simpa only [d790, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare811 (p : Pattern) (guard : d790 p = 1) : d74 p ≤ (2 : Int) + d844 p := by
  cases selected : p 108 with
  | false =>
    have hg : d790 p = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d790 p = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare810 p hg
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare812 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d336 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare813 (p : Pattern) (guard : d845 p = 1) : d67 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d845, d67, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare475 p hg
    simpa only [d845, d67, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, d67, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare812 p hg
    simpa only [d845, d67, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare814 (p : Pattern) (guard : d758 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  omega
theorem compare815 (p : Pattern) (guard : d818 p = 1) : d57 p ≤ (0 : Int) + d114 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare814 p hg
    simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare816 (p : Pattern) (guard : d818 p = 1) : d68 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare817 (p : Pattern) (guard : d758 p = 1) : d63 p ≤ (0 : Int) + d63 p := by
  omega
theorem compare818 (p : Pattern) (guard : d818 p = 1) : d63 p ≤ (0 : Int) + d116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare817 p hg
    simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare819 (p : Pattern) (guard : d818 p = 1) : d69 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare818 p hg
    simpa only [d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare820 (p : Pattern) (guard : d818 p = 1) : d70 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare819 p hg
    simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare821 (p : Pattern) (guard : d848 p = 1) : d71 p ≤ (0 : Int) + d341 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d848, d71, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare820 p hg
    simpa only [d848, d71, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d848, d71, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d848, d71, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare822 (p : Pattern) (guard : d849 p = 1) : d72 p ≤ (0 : Int) + d342 p := by
  cases selected : p 133 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d849, d72, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d849, d72, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d848 p = 1 := by simpa only [d849, d72, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare821 p hg
    simpa only [d849, d72, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare823 (p : Pattern) (guard : d845 p = 1) : d71 p ≤ (0 : Int) + d341 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d845, d71, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare523 p hg
    simpa only [d845, d71, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, d71, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d845, d71, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare824 (p : Pattern) (guard : d848 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare825 (p : Pattern) (guard : d849 p = 1) : d73 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d849, d73, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare823 p hg
    simpa only [d849, d73, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d848 p = 1 := by simpa only [d849, d73, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d849, d73, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare826 (p : Pattern) (guard : d849 p = 1) : d74 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d849 p = 1 := by simpa only [d74, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d74, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d849 p = 1 := by simpa only [d74, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare825 p hg
    simpa only [d74, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare827 (p : Pattern) (guard : d845 p = 1) : d67 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d845, d67, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare475 p hg
    simpa only [d845, d67, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, d67, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d845, d67, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare828 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare829 (p : Pattern) (guard : d758 p = 1) : d57 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d57, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d758, d57, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d57, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare828 p hg
    simpa only [d758, d57, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare830 (p : Pattern) (guard : d818 p = 1) : d57 p ≤ (0 : Int) + d346 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare829 p hg
    simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare831 (p : Pattern) (guard : d818 p = 1) : d68 p ≤ (0 : Int) + d347 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d68, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare830 p hg
    simpa only [d68, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d68, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d68, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare832 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (0 : Int) + d144 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare833 (p : Pattern) (guard : d758 p = 1) : d63 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d63, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d758, d63, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d63, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare832 p hg
    simpa only [d758, d63, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare834 (p : Pattern) (guard : d818 p = 1) : d63 p ≤ (0 : Int) + d348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare833 p hg
    simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare835 (p : Pattern) (guard : d818 p = 1) : d69 p ≤ (0 : Int) + d349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d69, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare834 p hg
    simpa only [d69, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d69, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d69, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare836 (p : Pattern) (guard : d818 p = 1) : d70 p ≤ (0 : Int) + d350 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d70, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d70, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d70, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare835 p hg
    simpa only [d70, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare837 (p : Pattern) (guard : d848 p = 1) : d71 p ≤ (0 : Int) + d351 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d848, d71, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare836 p hg
    simpa only [d848, d71, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d848, d71, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d848, d71, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare838 (p : Pattern) (guard : d849 p = 1) : d72 p ≤ (0 : Int) + d352 p := by
  cases selected : p 133 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d849, d72, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare827 p hg
    simpa only [d849, d72, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d848 p = 1 := by simpa only [d849, d72, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare837 p hg
    simpa only [d849, d72, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare839 (p : Pattern) (guard : d845 p = 1) : d71 p ≤ (0 : Int) + d353 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d845, d71, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare523 p hg
    simpa only [d845, d71, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, d71, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d845, d71, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
