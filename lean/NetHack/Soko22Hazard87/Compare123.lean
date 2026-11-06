import NetHack.Soko22Hazard87.Compare122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30750 (p : Pattern) (guard : d259866 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 118 with
  | false =>
    have hg : d259865 p = 1 := by simpa only [d259866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30749 p hg
    simpa only [d259866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30751 (p : Pattern) (guard : d259867 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 114 with
  | false =>
    have hg : d259866 p = 1 := by simpa only [d259867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30750 p hg
    simpa only [d259867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30752 (p : Pattern) (guard : d259868 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 111 with
  | false =>
    have hg : d259867 p = 1 := by simpa only [d259868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30751 p hg
    simpa only [d259868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30753 (p : Pattern) (guard : d259869 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 98 with
  | false =>
    have hg : d259868 p = 1 := by simpa only [d259869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30752 p hg
    simpa only [d259869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30754 (p : Pattern) (guard : d259870 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 97 with
  | false =>
    have hg : d259869 p = 1 := by simpa only [d259870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30753 p hg
    simpa only [d259870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30755 (p : Pattern) (guard : d259871 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 94 with
  | false =>
    have hg : d259870 p = 1 := by simpa only [d259871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30754 p hg
    simpa only [d259871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30756 (p : Pattern) (guard : d259872 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 76 with
  | false =>
    have hg : d259871 p = 1 := by simpa only [d259872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30755 p hg
    simpa only [d259872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30757 (p : Pattern) (guard : d259873 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 67 with
  | false =>
    have hg : d259872 p = 1 := by simpa only [d259873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30756 p hg
    simpa only [d259873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30758 (p : Pattern) (guard : d259874 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 52 with
  | false =>
    have hg : d259873 p = 1 := by simpa only [d259874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30757 p hg
    simpa only [d259874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30759 (p : Pattern) (guard : d259875 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 47 with
  | false =>
    have hg : d259874 p = 1 := by simpa only [d259875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30758 p hg
    simpa only [d259875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30760 (p : Pattern) (guard : d259876 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 46 with
  | false =>
    have hg : d259875 p = 1 := by simpa only [d259876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30759 p hg
    simpa only [d259876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30761 (p : Pattern) (guard : d259877 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 45 with
  | false =>
    have hg : d259876 p = 1 := by simpa only [d259877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30760 p hg
    simpa only [d259877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30762 (p : Pattern) (guard : d259878 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 30 with
  | false =>
    have hg : d259877 p = 1 := by simpa only [d259878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30761 p hg
    simpa only [d259878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30763 (p : Pattern) (guard : d259879 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 29 with
  | false =>
    have hg : d259878 p = 1 := by simpa only [d259879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30762 p hg
    simpa only [d259879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30764 (p : Pattern) (guard : d259880 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 28 with
  | false =>
    have hg : d259879 p = 1 := by simpa only [d259880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30763 p hg
    simpa only [d259880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30765 (p : Pattern) (guard : d259881 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 27 with
  | false =>
    have hg : d259880 p = 1 := by simpa only [d259881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30764 p hg
    simpa only [d259881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30766 (p : Pattern) (guard : d259882 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 25 with
  | false =>
    have hg : d259881 p = 1 := by simpa only [d259882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30765 p hg
    simpa only [d259882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30767 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30768 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30769 (p : Pattern) (guard : d0 p = 1) : d47697 p ≤ (-2 : Int) + d253344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30770 (p : Pattern) (guard : d0 p = 1) : d47676 p ≤ (-2 : Int) + d253323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30771 (p : Pattern) (guard : d0 p = 1) : d47681 p ≤ (-2 : Int) + d253328 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30772 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (-2 : Int) + d253304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30773 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30774 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (-2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30775 (p : Pattern) (guard : d44880 p = 1) : d4 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44880, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30774 p hg
    simpa only [d44880, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13 p = 1 := by simpa only [d44880, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d44880, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30776 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (-2 : Int) + d47616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30777 (p : Pattern) (guard : d46864 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30775 p hg
    simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30776 p hg
    simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30778 (p : Pattern) (guard : d46865 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30777 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30779 (p : Pattern) (guard : d46866 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30778 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30780 (p : Pattern) (guard : d258695 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30779 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30781 (p : Pattern) (guard : d258696 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258695 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30780 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30782 (p : Pattern) (guard : d258697 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258696 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30781 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30783 (p : Pattern) (guard : d258698 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258697 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30782 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30784 (p : Pattern) (guard : d258699 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258698 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30783 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30785 (p : Pattern) (guard : d0 p = 1) : d47618 p ≤ (-2 : Int) + d253275 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30786 (p : Pattern) (guard : d258700 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258699 p = 1 := by simpa only [d258700, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30784 p hg
    simpa only [d258700, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258700, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d258700, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30787 (p : Pattern) (guard : d0 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30788 (p : Pattern) (guard : d258701 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258700 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30786 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30787 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30789 (p : Pattern) (guard : d0 p = 1) : d47659 p ≤ (-2 : Int) + d253306 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30790 (p : Pattern) (guard : d258702 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258701 p = 1 := by simpa only [d258702, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30788 p hg
    simpa only [d258702, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258702, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d258702, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30791 (p : Pattern) (guard : d0 p = 1) : d47662 p ≤ (-2 : Int) + d253309 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30792 (p : Pattern) (guard : d258703 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258702 p = 1 := by simpa only [d258703, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30790 p hg
    simpa only [d258703, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258703, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d258703, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30793 (p : Pattern) (guard : d258704 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258704, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d258704, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258703 p = 1 := by simpa only [d258704, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30792 p hg
    simpa only [d258704, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30794 (p : Pattern) (guard : d0 p = 1) : d47684 p ≤ (-2 : Int) + d253331 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30795 (p : Pattern) (guard : d258705 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258704 p = 1 := by simpa only [d258705, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30793 p hg
    simpa only [d258705, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258705, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d258705, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30796 (p : Pattern) (guard : d0 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30797 (p : Pattern) (guard : d258706 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258705 p = 1 := by simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30795 p hg
    simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30798 (p : Pattern) (guard : d258707 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258706 p = 1 := by simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30797 p hg
    simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30799 (p : Pattern) (guard : d258708 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258707 p = 1 := by simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30798 p hg
    simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30800 (p : Pattern) (guard : d258709 p = 1) : d47686 p ≤ (-2 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258709, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30771 p hg
    simpa only [d258709, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258708 p = 1 := by simpa only [d258709, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30799 p hg
    simpa only [d258709, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30801 (p : Pattern) (guard : d258710 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258710, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30770 p hg
    simpa only [d258710, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258709 p = 1 := by simpa only [d258710, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30800 p hg
    simpa only [d258710, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30802 (p : Pattern) (guard : d0 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30803 (p : Pattern) (guard : d258711 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258710 p = 1 := by simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30801 p hg
    simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30804 (p : Pattern) (guard : d258712 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258711 p = 1 := by simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30803 p hg
    simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30805 (p : Pattern) (guard : d258713 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258712 p = 1 := by simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30804 p hg
    simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30806 (p : Pattern) (guard : d0 p = 1) : d47698 p ≤ (-2 : Int) + d253345 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30807 (p : Pattern) (guard : d258714 p = 1) : d47699 p ≤ (-2 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258713 p = 1 := by simpa only [d258714, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30805 p hg
    simpa only [d258714, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258714, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d258714, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30808 (p : Pattern) (guard : d258715 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258715, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d258715, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258714 p = 1 := by simpa only [d258715, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30807 p hg
    simpa only [d258715, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30809 (p : Pattern) (guard : d258716 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258715 p = 1 := by simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30808 p hg
    simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30810 (p : Pattern) (guard : d258717 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258716 p = 1 := by simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30809 p hg
    simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30811 (p : Pattern) (guard : d258718 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258717 p = 1 := by simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30810 p hg
    simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30812 (p : Pattern) (guard : d258719 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258718 p = 1 := by simpa only [d258719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30811 p hg
    simpa only [d258719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30813 (p : Pattern) (guard : d258720 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258719 p = 1 := by simpa only [d258720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30812 p hg
    simpa only [d258720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30814 (p : Pattern) (guard : d258779 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258720 p = 1 := by simpa only [d258779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30813 p hg
    simpa only [d258779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30815 (p : Pattern) (guard : d258780 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258779 p = 1 := by simpa only [d258780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30814 p hg
    simpa only [d258780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30816 (p : Pattern) (guard : d258781 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258780 p = 1 := by simpa only [d258781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30815 p hg
    simpa only [d258781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30817 (p : Pattern) (guard : d258782 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258781 p = 1 := by simpa only [d258782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30816 p hg
    simpa only [d258782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30818 (p : Pattern) (guard : d258783 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258782 p = 1 := by simpa only [d258783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30817 p hg
    simpa only [d258783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30819 (p : Pattern) (guard : d258726 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258718 p = 1 := by simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30811 p hg
    simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30820 (p : Pattern) (guard : d258727 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258726 p = 1 := by simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30819 p hg
    simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30821 (p : Pattern) (guard : d258786 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258727 p = 1 := by simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30820 p hg
    simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30822 (p : Pattern) (guard : d258787 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258786 p = 1 := by simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30821 p hg
    simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30823 (p : Pattern) (guard : d258788 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258787 p = 1 := by simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30822 p hg
    simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30824 (p : Pattern) (guard : d258789 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258788 p = 1 := by simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30823 p hg
    simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30825 (p : Pattern) (guard : d258790 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258782 p = 1 := by simpa only [d258790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30817 p hg
    simpa only [d258790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258789 p = 1 := by simpa only [d258790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30824 p hg
    simpa only [d258790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30826 (p : Pattern) (guard : d258791 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258783 p = 1 := by simpa only [d258791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30818 p hg
    simpa only [d258791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258790 p = 1 := by simpa only [d258791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30825 p hg
    simpa only [d258791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30827 (p : Pattern) (guard : d258792 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258791 p = 1 := by simpa only [d258792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30826 p hg
    simpa only [d258792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30828 (p : Pattern) (guard : d260087 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258792 p = 1 := by simpa only [d260087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30827 p hg
    simpa only [d260087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30829 (p : Pattern) (guard : d260088 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260087 p = 1 := by simpa only [d260088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30828 p hg
    simpa only [d260088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30830 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30831 (p : Pattern) (guard : d0 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30832 (p : Pattern) (guard : d0 p = 1) : d47763 p ≤ (-2 : Int) + d253402 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30833 (p : Pattern) (guard : d0 p = 1) : d47746 p ≤ (-2 : Int) + d253385 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30834 (p : Pattern) (guard : d0 p = 1) : d47751 p ≤ (-2 : Int) + d253390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30835 (p : Pattern) (guard : d0 p = 1) : d47734 p ≤ (-2 : Int) + d253373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30836 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30837 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (-2 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30838 (p : Pattern) (guard : d44880 p = 1) : d5 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44880, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30837 p hg
    simpa only [d44880, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13 p = 1 := by simpa only [d44880, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8178 p hg
    simpa only [d44880, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30839 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (-2 : Int) + d47705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30840 (p : Pattern) (guard : d46864 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30838 p hg
    simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30839 p hg
    simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30841 (p : Pattern) (guard : d46865 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30840 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30842 (p : Pattern) (guard : d46866 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30841 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30843 (p : Pattern) (guard : d258695 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30842 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30844 (p : Pattern) (guard : d258696 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258695 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30843 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30845 (p : Pattern) (guard : d258697 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258696 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30844 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30846 (p : Pattern) (guard : d258698 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258697 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30845 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30847 (p : Pattern) (guard : d258699 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258698 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30846 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30848 (p : Pattern) (guard : d0 p = 1) : d47707 p ≤ (-2 : Int) + d253350 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30849 (p : Pattern) (guard : d258700 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258699 p = 1 := by simpa only [d258700, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30847 p hg
    simpa only [d258700, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258700, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d258700, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30850 (p : Pattern) (guard : d0 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30851 (p : Pattern) (guard : d258701 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258700 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30849 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30850 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30852 (p : Pattern) (guard : d0 p = 1) : d47661 p ≤ (-2 : Int) + d253308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30853 (p : Pattern) (guard : d258702 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258701 p = 1 := by simpa only [d258702, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30851 p hg
    simpa only [d258702, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258702, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258702, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30854 (p : Pattern) (guard : d258703 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258702 p = 1 := by simpa only [d258703, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30853 p hg
    simpa only [d258703, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258703, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258703, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30855 (p : Pattern) (guard : d258704 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258704, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d258704, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258703 p = 1 := by simpa only [d258704, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30854 p hg
    simpa only [d258704, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30856 (p : Pattern) (guard : d0 p = 1) : d47754 p ≤ (-2 : Int) + d253393 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30857 (p : Pattern) (guard : d258705 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258704 p = 1 := by simpa only [d258705, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30855 p hg
    simpa only [d258705, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258705, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d258705, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30858 (p : Pattern) (guard : d0 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30859 (p : Pattern) (guard : d258706 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258705 p = 1 := by simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30860 (p : Pattern) (guard : d258707 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258706 p = 1 := by simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30859 p hg
    simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30861 (p : Pattern) (guard : d258708 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258707 p = 1 := by simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30860 p hg
    simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30862 (p : Pattern) (guard : d258709 p = 1) : d47756 p ≤ (-2 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258709, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30834 p hg
    simpa only [d258709, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258708 p = 1 := by simpa only [d258709, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30861 p hg
    simpa only [d258709, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30863 (p : Pattern) (guard : d258710 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258710, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d258710, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258709 p = 1 := by simpa only [d258710, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30862 p hg
    simpa only [d258710, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30864 (p : Pattern) (guard : d0 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30865 (p : Pattern) (guard : d258711 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258710 p = 1 := by simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30863 p hg
    simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30866 (p : Pattern) (guard : d258712 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258711 p = 1 := by simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30865 p hg
    simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30867 (p : Pattern) (guard : d258713 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258712 p = 1 := by simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30866 p hg
    simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30868 (p : Pattern) (guard : d0 p = 1) : d47764 p ≤ (-2 : Int) + d253403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30869 (p : Pattern) (guard : d258714 p = 1) : d47765 p ≤ (-2 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258713 p = 1 := by simpa only [d258714, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30867 p hg
    simpa only [d258714, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258714, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d258714, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30870 (p : Pattern) (guard : d258715 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258715, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d258715, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258714 p = 1 := by simpa only [d258715, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30869 p hg
    simpa only [d258715, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30871 (p : Pattern) (guard : d258716 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258715 p = 1 := by simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30870 p hg
    simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30872 (p : Pattern) (guard : d258717 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258716 p = 1 := by simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30871 p hg
    simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30873 (p : Pattern) (guard : d258718 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258717 p = 1 := by simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30874 (p : Pattern) (guard : d258726 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258718 p = 1 := by simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30873 p hg
    simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30875 (p : Pattern) (guard : d258727 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258726 p = 1 := by simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30874 p hg
    simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30876 (p : Pattern) (guard : d258786 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258727 p = 1 := by simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30875 p hg
    simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30877 (p : Pattern) (guard : d258787 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258786 p = 1 := by simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30876 p hg
    simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30878 (p : Pattern) (guard : d258788 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258787 p = 1 := by simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30877 p hg
    simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30879 (p : Pattern) (guard : d258789 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258788 p = 1 := by simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30878 p hg
    simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30880 (p : Pattern) (guard : d259008 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259008, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259008, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258789 p = 1 := by simpa only [d259008, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30879 p hg
    simpa only [d259008, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30881 (p : Pattern) (guard : d259009 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d259009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259008 p = 1 := by simpa only [d259009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30880 p hg
    simpa only [d259009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30882 (p : Pattern) (guard : d260089 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259009 p = 1 := by simpa only [d260089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30881 p hg
    simpa only [d260089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30883 (p : Pattern) (guard : d260090 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260089 p = 1 := by simpa only [d260090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30882 p hg
    simpa only [d260090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30884 (p : Pattern) (guard : d260091 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260090 p = 1 := by simpa only [d260091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30883 p hg
    simpa only [d260091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30885 (p : Pattern) (guard : d260092 p = 1) : d47768 p ≤ (-2 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260088 p = 1 := by simpa only [d260092, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30829 p hg
    simpa only [d260092, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260091 p = 1 := by simpa only [d260092, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30884 p hg
    simpa only [d260092, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30886 (p : Pattern) (guard : d0 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30887 (p : Pattern) (guard : d0 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30888 (p : Pattern) (guard : d0 p = 1) : d47786 p ≤ (-2 : Int) + d253425 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30889 (p : Pattern) (guard : d0 p = 1) : d47796 p ≤ (-2 : Int) + d253433 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30890 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30891 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30892 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (-2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30893 (p : Pattern) (guard : d44880 p = 1) : d2 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44880, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30892 p hg
    simpa only [d44880, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13 p = 1 := by simpa only [d44880, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8220 p hg
    simpa only [d44880, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30894 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (-2 : Int) + d47629 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30895 (p : Pattern) (guard : d46864 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30893 p hg
    simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30894 p hg
    simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30896 (p : Pattern) (guard : d46865 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30895 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30897 (p : Pattern) (guard : d46866 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30896 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30898 (p : Pattern) (guard : d258695 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30897 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30899 (p : Pattern) (guard : d258696 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258695 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30898 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30900 (p : Pattern) (guard : d258697 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258696 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30899 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30901 (p : Pattern) (guard : d258698 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258697 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30900 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30902 (p : Pattern) (guard : d258699 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258698 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30901 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30903 (p : Pattern) (guard : d0 p = 1) : d47631 p ≤ (-2 : Int) + d253284 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30904 (p : Pattern) (guard : d258700 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258699 p = 1 := by simpa only [d258700, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30902 p hg
    simpa only [d258700, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258700, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d258700, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30905 (p : Pattern) (guard : d258701 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258700 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30904 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30906 (p : Pattern) (guard : d258743 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d258743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258701 p = 1 := by simpa only [d258743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30905 p hg
    simpa only [d258743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30907 (p : Pattern) (guard : d258702 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258701 p = 1 := by simpa only [d258702, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30788 p hg
    simpa only [d258702, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258702, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258702, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30908 (p : Pattern) (guard : d258744 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258743 p = 1 := by simpa only [d258744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30906 p hg
    simpa only [d258744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258702 p = 1 := by simpa only [d258744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30907 p hg
    simpa only [d258744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30909 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30910 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (-2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30911 (p : Pattern) (guard : d44880 p = 1) : d6 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44880, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30910 p hg
    simpa only [d44880, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13 p = 1 := by simpa only [d44880, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8236 p hg
    simpa only [d44880, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30912 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (-2 : Int) + d47633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30913 (p : Pattern) (guard : d46864 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30911 p hg
    simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30912 p hg
    simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30914 (p : Pattern) (guard : d46865 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30913 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30915 (p : Pattern) (guard : d46866 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30914 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30916 (p : Pattern) (guard : d258695 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30915 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30917 (p : Pattern) (guard : d258696 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258695 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30916 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30918 (p : Pattern) (guard : d258697 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258696 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30917 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30919 (p : Pattern) (guard : d258698 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258697 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30918 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30920 (p : Pattern) (guard : d258699 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258698 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30919 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30921 (p : Pattern) (guard : d0 p = 1) : d47635 p ≤ (-2 : Int) + d253286 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30922 (p : Pattern) (guard : d258700 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258699 p = 1 := by simpa only [d258700, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30920 p hg
    simpa only [d258700, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258700, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d258700, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30923 (p : Pattern) (guard : d0 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30924 (p : Pattern) (guard : d258701 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258700 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30922 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30923 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30925 (p : Pattern) (guard : d258702 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258701 p = 1 := by simpa only [d258702, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30924 p hg
    simpa only [d258702, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258702, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258702, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30926 (p : Pattern) (guard : d258703 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258702 p = 1 := by simpa only [d258703, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30925 p hg
    simpa only [d258703, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258703, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258703, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30927 (p : Pattern) (guard : d258745 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d258744 p = 1 := by simpa only [d258745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30908 p hg
    simpa only [d258745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258703 p = 1 := by simpa only [d258745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30926 p hg
    simpa only [d258745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30928 (p : Pattern) (guard : d0 p = 1) : d47802 p ≤ (-2 : Int) + d253439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30929 (p : Pattern) (guard : d258746 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258745 p = 1 := by simpa only [d258746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30927 p hg
    simpa only [d258746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d258746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30930 (p : Pattern) (guard : d0 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30931 (p : Pattern) (guard : d258747 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258746 p = 1 := by simpa only [d258747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30929 p hg
    simpa only [d258747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d258747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30932 (p : Pattern) (guard : d258748 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258747 p = 1 := by simpa only [d258748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30931 p hg
    simpa only [d258748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d258748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30933 (p : Pattern) (guard : d258749 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258748 p = 1 := by simpa only [d258749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30932 p hg
    simpa only [d258749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d258749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30934 (p : Pattern) (guard : d258750 p = 1) : d47804 p ≤ (-2 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258750, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30889 p hg
    simpa only [d258750, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258749 p = 1 := by simpa only [d258750, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30933 p hg
    simpa only [d258750, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30935 (p : Pattern) (guard : d258751 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258751, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30888 p hg
    simpa only [d258751, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258750 p = 1 := by simpa only [d258751, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30934 p hg
    simpa only [d258751, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30936 (p : Pattern) (guard : d0 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30937 (p : Pattern) (guard : d258752 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258751 p = 1 := by simpa only [d258752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30935 p hg
    simpa only [d258752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d258752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30938 (p : Pattern) (guard : d258753 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258752 p = 1 := by simpa only [d258753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30937 p hg
    simpa only [d258753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d258753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30939 (p : Pattern) (guard : d258754 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258753 p = 1 := by simpa only [d258754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30938 p hg
    simpa only [d258754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d258754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30940 (p : Pattern) (guard : d0 p = 1) : d47806 p ≤ (-2 : Int) + d253443 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30941 (p : Pattern) (guard : d258755 p = 1) : d47807 p ≤ (-2 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258754 p = 1 := by simpa only [d258755, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30939 p hg
    simpa only [d258755, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258755, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d258755, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30942 (p : Pattern) (guard : d258756 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258756, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d258756, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258755 p = 1 := by simpa only [d258756, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30941 p hg
    simpa only [d258756, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30943 (p : Pattern) (guard : d258757 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258756 p = 1 := by simpa only [d258757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30942 p hg
    simpa only [d258757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d258757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30944 (p : Pattern) (guard : d258758 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258757 p = 1 := by simpa only [d258758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30943 p hg
    simpa only [d258758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d258758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30945 (p : Pattern) (guard : d258759 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258758 p = 1 := by simpa only [d258759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30944 p hg
    simpa only [d258759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d258759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30946 (p : Pattern) (guard : d258760 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258759 p = 1 := by simpa only [d258760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30945 p hg
    simpa only [d258760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d258760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30947 (p : Pattern) (guard : d258761 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258760 p = 1 := by simpa only [d258761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30946 p hg
    simpa only [d258761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d258761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30948 (p : Pattern) (guard : d259050 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258761 p = 1 := by simpa only [d259050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30947 p hg
    simpa only [d259050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30949 (p : Pattern) (guard : d259051 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259050 p = 1 := by simpa only [d259051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30948 p hg
    simpa only [d259051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30950 (p : Pattern) (guard : d259052 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259051 p = 1 := by simpa only [d259052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30949 p hg
    simpa only [d259052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30951 (p : Pattern) (guard : d259053 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259052 p = 1 := by simpa only [d259053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30950 p hg
    simpa only [d259053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30952 (p : Pattern) (guard : d259054 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259054, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259054, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259053 p = 1 := by simpa only [d259054, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30951 p hg
    simpa only [d259054, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30953 (p : Pattern) (guard : d259055 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d259055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259054 p = 1 := by simpa only [d259055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30952 p hg
    simpa only [d259055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30954 (p : Pattern) (guard : d260093 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259055 p = 1 := by simpa only [d260093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30953 p hg
    simpa only [d260093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30955 (p : Pattern) (guard : d260094 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260093 p = 1 := by simpa only [d260094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30954 p hg
    simpa only [d260094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30956 (p : Pattern) (guard : d260095 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260094 p = 1 := by simpa only [d260095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30955 p hg
    simpa only [d260095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30957 (p : Pattern) (guard : d0 p = 1) : d47864 p ≤ (-2 : Int) + d253501 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30958 (p : Pattern) (guard : d260096 p = 1) : d47865 p ≤ (-2 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260095 p = 1 := by simpa only [d260096, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30956 p hg
    simpa only [d260096, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260096, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30957 p hg
    simpa only [d260096, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30959 (p : Pattern) (guard : d260097 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d260092 p = 1 := by simpa only [d260097, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30885 p hg
    simpa only [d260097, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260096 p = 1 := by simpa only [d260097, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30958 p hg
    simpa only [d260097, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30960 (p : Pattern) (guard : d260098 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260097 p = 1 := by simpa only [d260098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30959 p hg
    simpa only [d260098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30961 (p : Pattern) (guard : d260099 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260098 p = 1 := by simpa only [d260099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30960 p hg
    simpa only [d260099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30962 (p : Pattern) (guard : d260100 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260099 p = 1 := by simpa only [d260100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30961 p hg
    simpa only [d260100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30963 (p : Pattern) (guard : d260101 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260100 p = 1 := by simpa only [d260101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30962 p hg
    simpa only [d260101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30964 (p : Pattern) (guard : d260102 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260101 p = 1 := by simpa only [d260102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30963 p hg
    simpa only [d260102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30965 (p : Pattern) (guard : d260103 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260102 p = 1 := by simpa only [d260103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30964 p hg
    simpa only [d260103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30966 (p : Pattern) (guard : d260104 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260103 p = 1 := by simpa only [d260104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30965 p hg
    simpa only [d260104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30967 (p : Pattern) (guard : d307 p = 1) : d4 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d307, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30774 p hg
    simpa only [d307, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d127 p = 1 := by simpa only [d307, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8285 p hg
    simpa only [d307, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30968 (p : Pattern) (guard : d1997 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30967 p hg
    simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30776 p hg
    simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30969 (p : Pattern) (guard : d258806 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30968 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46864 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30777 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30970 (p : Pattern) (guard : d258807 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30969 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30778 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30971 (p : Pattern) (guard : d258808 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258807 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30970 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30972 (p : Pattern) (guard : d258809 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258808 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30971 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30973 (p : Pattern) (guard : d258810 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258809 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30972 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30974 (p : Pattern) (guard : d258811 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258810 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30973 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30975 (p : Pattern) (guard : d258812 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30974 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258698 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30783 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30976 (p : Pattern) (guard : d258813 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258812 p = 1 := by simpa only [d258813, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30975 p hg
    simpa only [d258813, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258813, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d258813, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30977 (p : Pattern) (guard : d258814 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258813 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30976 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30786 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30978 (p : Pattern) (guard : d258815 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258814 p = 1 := by simpa only [d258815, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30977 p hg
    simpa only [d258815, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258815, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d258815, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30979 (p : Pattern) (guard : d258816 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258815 p = 1 := by simpa only [d258816, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30978 p hg
    simpa only [d258816, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258816, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d258816, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30980 (p : Pattern) (guard : d258817 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258817, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d258817, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258816 p = 1 := by simpa only [d258817, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30979 p hg
    simpa only [d258817, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30981 (p : Pattern) (guard : d258818 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258817 p = 1 := by simpa only [d258818, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30980 p hg
    simpa only [d258818, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258818, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d258818, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30982 (p : Pattern) (guard : d258819 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258818 p = 1 := by simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30981 p hg
    simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258705 p = 1 := by simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30795 p hg
    simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30983 (p : Pattern) (guard : d258820 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258819 p = 1 := by simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30982 p hg
    simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258706 p = 1 := by simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30797 p hg
    simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30984 (p : Pattern) (guard : d258821 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258820 p = 1 := by simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30983 p hg
    simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258707 p = 1 := by simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30798 p hg
    simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30985 (p : Pattern) (guard : d258822 p = 1) : d47686 p ≤ (-2 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258822, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30771 p hg
    simpa only [d258822, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258821 p = 1 := by simpa only [d258822, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30984 p hg
    simpa only [d258822, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30986 (p : Pattern) (guard : d258823 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258823, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30770 p hg
    simpa only [d258823, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258822 p = 1 := by simpa only [d258823, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30985 p hg
    simpa only [d258823, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30987 (p : Pattern) (guard : d258824 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258823 p = 1 := by simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30986 p hg
    simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258710 p = 1 := by simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30801 p hg
    simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30988 (p : Pattern) (guard : d258825 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258824 p = 1 := by simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30987 p hg
    simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258711 p = 1 := by simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30803 p hg
    simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30989 (p : Pattern) (guard : d258826 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258825 p = 1 := by simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30988 p hg
    simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30990 (p : Pattern) (guard : d258827 p = 1) : d47699 p ≤ (-2 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258826 p = 1 := by simpa only [d258827, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30989 p hg
    simpa only [d258827, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258827, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d258827, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30991 (p : Pattern) (guard : d258828 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258828, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d258828, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258827 p = 1 := by simpa only [d258828, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30990 p hg
    simpa only [d258828, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30992 (p : Pattern) (guard : d258829 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258828 p = 1 := by simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30991 p hg
    simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258715 p = 1 := by simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30808 p hg
    simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30993 (p : Pattern) (guard : d258830 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258829 p = 1 := by simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30992 p hg
    simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30994 (p : Pattern) (guard : d258831 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258830 p = 1 := by simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30993 p hg
    simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30995 (p : Pattern) (guard : d258832 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258831 p = 1 := by simpa only [d258832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30994 p hg
    simpa only [d258832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30996 (p : Pattern) (guard : d258833 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258832 p = 1 := by simpa only [d258833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30995 p hg
    simpa only [d258833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258719 p = 1 := by simpa only [d258833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30812 p hg
    simpa only [d258833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30997 (p : Pattern) (guard : d258906 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258833 p = 1 := by simpa only [d258906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30996 p hg
    simpa only [d258906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30998 (p : Pattern) (guard : d258907 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258906 p = 1 := by simpa only [d258907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30997 p hg
    simpa only [d258907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30999 (p : Pattern) (guard : d258908 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258907 p = 1 := by simpa only [d258908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30998 p hg
    simpa only [d258908, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
