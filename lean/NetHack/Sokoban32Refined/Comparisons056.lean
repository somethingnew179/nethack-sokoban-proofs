/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7840 (p : Pattern) (guard : d0 p = 1) : d719 p ≤ (3 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7841 (p : Pattern) (guard : d917 p = 1) : d719 p ≤ (3 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7783 p hg
    simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7811 p hg
    simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7842 (p : Pattern) (guard : d918 p = 1) : d719 p ≤ (3 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7840 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7841 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7843 (p : Pattern) (guard : d0 p = 1) : d719 p ≤ (3 : Int) + d92 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7844 (p : Pattern) (guard : d917 p = 1) : d719 p ≤ (3 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d719, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7796 p hg
    simpa only [d719, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d719, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d719, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7845 (p : Pattern) (guard : d918 p = 1) : d719 p ≤ (3 : Int) + d92 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7843 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7844 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7846 (p : Pattern) (guard : d918 p = 1) : d719 p ≤ (3 : Int) + d1196 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7842 p hg
    simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7845 p hg
    simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7847 (p : Pattern) (guard : d918 p = 1) : d719 p ≤ (3 : Int) + d1197 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7842 p hg
    simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7846 p hg
    simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7848 (p : Pattern) (guard : d918 p = 1) : d720 p ≤ (3 : Int) + d1198 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d720, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7803 p hg
    simpa only [d720, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d720, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7847 p hg
    simpa only [d720, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7849 (p : Pattern) (guard : d0 p = 1) : d706 p ≤ (3 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7850 (p : Pattern) (guard : d917 p = 1) : d705 p ≤ (3 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7790 p hg
    simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7781 p hg
    simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7851 (p : Pattern) (guard : d917 p = 1) : d706 p ≤ (3 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7790 p hg
    simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7850 p hg
    simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7852 (p : Pattern) (guard : d918 p = 1) : d706 p ≤ (3 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7849 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7851 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7853 (p : Pattern) (guard : d918 p = 1) : d706 p ≤ (3 : Int) + d1199 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7852 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7825 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7854 (p : Pattern) (guard : d918 p = 1) : d706 p ≤ (3 : Int) + d1200 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7852 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7853 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7855 (p : Pattern) (guard : d918 p = 1) : d721 p ≤ (3 : Int) + d1201 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d721, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7848 p hg
    simpa only [d721, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d721, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7854 p hg
    simpa only [d721, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7856 (p : Pattern) (guard : d918 p = 1) : d722 p ≤ (3 : Int) + d1202 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d722, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7842 p hg
    simpa only [d722, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d722, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d722, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7857 (p : Pattern) (guard : d918 p = 1) : d723 p ≤ (3 : Int) + d1203 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d723, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7842 p hg
    simpa only [d723, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d723, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7856 p hg
    simpa only [d723, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7858 (p : Pattern) (guard : d918 p = 1) : d724 p ≤ (3 : Int) + d1204 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d724, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7831 p hg
    simpa only [d724, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d724, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7857 p hg
    simpa only [d724, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7859 (p : Pattern) (guard : d918 p = 1) : d2 p ≤ (3 : Int) + d2 p := by
  omega
theorem compare7860 (p : Pattern) (guard : d918 p = 1) : d725 p ≤ (3 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d725, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7852 p hg
    simpa only [d725, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d725, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7859 p hg
    simpa only [d725, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7861 (p : Pattern) (guard : d918 p = 1) : d726 p ≤ (3 : Int) + d1205 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d726, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7852 p hg
    simpa only [d726, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d726, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7860 p hg
    simpa only [d726, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7862 (p : Pattern) (guard : d0 p = 1) : d705 p ≤ (3 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7863 (p : Pattern) (guard : d918 p = 1) : d705 p ≤ (3 : Int) + d97 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7862 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7850 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7864 (p : Pattern) (guard : d918 p = 1) : d727 p ≤ (3 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d727, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7863 p hg
    simpa only [d727, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d727, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7859 p hg
    simpa only [d727, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7865 (p : Pattern) (guard : d918 p = 1) : d728 p ≤ (3 : Int) + d1206 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d728, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7863 p hg
    simpa only [d728, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d728, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7864 p hg
    simpa only [d728, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7866 (p : Pattern) (guard : d918 p = 1) : d729 p ≤ (3 : Int) + d1207 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d729, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7861 p hg
    simpa only [d729, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d729, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7865 p hg
    simpa only [d729, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7867 (p : Pattern) (guard : d918 p = 1) : d730 p ≤ (3 : Int) + d1208 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d730, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7858 p hg
    simpa only [d730, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d730, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7866 p hg
    simpa only [d730, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7868 (p : Pattern) (guard : d918 p = 1) : d731 p ≤ (3 : Int) + d1209 p := by
  cases selected : p 106 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d731, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7855 p hg
    simpa only [d731, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d731, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7867 p hg
    simpa only [d731, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7869 (p : Pattern) (guard : d918 p = 1) : d732 p ≤ (3 : Int) + d1210 p := by
  cases selected : p 86 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d732, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7839 p hg
    simpa only [d732, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d732, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7868 p hg
    simpa only [d732, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7870 (p : Pattern) (guard : d918 p = 1) : d733 p ≤ (3 : Int) + d1211 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d733, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7831 p hg
    simpa only [d733, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d733, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7837 p hg
    simpa only [d733, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7871 (p : Pattern) (guard : d918 p = 1) : d734 p ≤ (3 : Int) + d1212 p := by
  cases selected : p 106 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d734, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7821 p hg
    simpa only [d734, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d734, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7870 p hg
    simpa only [d734, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7872 (p : Pattern) (guard : d918 p = 1) : d705 p ≤ (3 : Int) + d1213 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7863 p hg
    simpa only [d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7873 (p : Pattern) (guard : d918 p = 1) : d705 p ≤ (3 : Int) + d1214 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7863 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7872 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7874 (p : Pattern) (guard : d918 p = 1) : d735 p ≤ (3 : Int) + d1215 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d735, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7854 p hg
    simpa only [d735, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d735, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7873 p hg
    simpa only [d735, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7875 (p : Pattern) (guard : d918 p = 1) : d736 p ≤ (3 : Int) + d1216 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d736, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7848 p hg
    simpa only [d736, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d736, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7874 p hg
    simpa only [d736, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7876 (p : Pattern) (guard : d918 p = 1) : d737 p ≤ (3 : Int) + d1217 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d737, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7831 p hg
    simpa only [d737, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d737, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7836 p hg
    simpa only [d737, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7877 (p : Pattern) (guard : d918 p = 1) : d738 p ≤ (3 : Int) + d1218 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d738, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7865 p hg
    simpa only [d738, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d738, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7859 p hg
    simpa only [d738, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7878 (p : Pattern) (guard : d918 p = 1) : d739 p ≤ (3 : Int) + d1219 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d739, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7876 p hg
    simpa only [d739, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d739, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7877 p hg
    simpa only [d739, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7879 (p : Pattern) (guard : d918 p = 1) : d740 p ≤ (3 : Int) + d1220 p := by
  cases selected : p 106 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d740, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7875 p hg
    simpa only [d740, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d740, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7878 p hg
    simpa only [d740, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7880 (p : Pattern) (guard : d918 p = 1) : d741 p ≤ (3 : Int) + d1221 p := by
  cases selected : p 86 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d741, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7871 p hg
    simpa only [d741, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d741, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7879 p hg
    simpa only [d741, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7881 (p : Pattern) (guard : d918 p = 1) : d742 p ≤ (3 : Int) + d1222 p := by
  cases selected : p 80 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d742, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7869 p hg
    simpa only [d742, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d742, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7880 p hg
    simpa only [d742, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7882 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d3 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7883 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d1293, d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7884 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d743 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7882 p hg
    simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7883 p hg
    simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7885 (p : Pattern) (guard : d1293 p = 1) : d37 p ≤ (0 : Int) + d744 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d37, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7882 p hg
    simpa only [d37, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d37, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d37, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7886 (p : Pattern) (guard : d1293 p = 1) : d697 p ≤ (0 : Int) + d745 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d697, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7884 p hg
    simpa only [d697, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d697, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7885 p hg
    simpa only [d697, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7887 (p : Pattern) (guard : d1293 p = 1) : d11 p ≤ (0 : Int) + d9 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3984 p hg
    simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7888 (p : Pattern) (guard : d1293 p = 1) : d11 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3984 p hg
    simpa only [d1293, d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7889 (p : Pattern) (guard : d1293 p = 1) : d11 p ≤ (0 : Int) + d746 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7887 p hg
    simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7888 p hg
    simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7890 (p : Pattern) (guard : d1293 p = 1) : d39 p ≤ (0 : Int) + d747 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d39, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7887 p hg
    simpa only [d39, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d39, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d39, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7891 (p : Pattern) (guard : d1293 p = 1) : d698 p ≤ (0 : Int) + d748 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d698, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7889 p hg
    simpa only [d698, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d698, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7890 p hg
    simpa only [d698, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7892 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d749 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d699, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7886 p hg
    simpa only [d699, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d699, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7891 p hg
    simpa only [d699, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7893 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d750 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d700, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7886 p hg
    simpa only [d700, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d700, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7892 p hg
    simpa only [d700, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7894 (p : Pattern) (guard : d1293 p = 1) : d37 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7883 p hg
    simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7895 (p : Pattern) (guard : d1293 p = 1) : d697 p ≤ (0 : Int) + d751 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d697, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7884 p hg
    simpa only [d697, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d697, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7894 p hg
    simpa only [d697, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7896 (p : Pattern) (guard : d1293 p = 1) : d39 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7888 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7897 (p : Pattern) (guard : d1293 p = 1) : d698 p ≤ (0 : Int) + d752 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d698, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7889 p hg
    simpa only [d698, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d698, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7896 p hg
    simpa only [d698, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7898 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d753 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d699, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7895 p hg
    simpa only [d699, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d699, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7897 p hg
    simpa only [d699, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7899 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d754 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d700, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7895 p hg
    simpa only [d700, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d700, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7898 p hg
    simpa only [d700, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7900 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d755 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7893 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7899 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7901 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d756 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7893 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7900 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7902 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d757 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7900 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7899 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7903 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d758 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7901 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7902 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7904 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d759 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7892 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7898 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7905 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d760 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7892 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7904 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7906 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d761 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7904 p hg
    simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7898 p hg
    simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7907 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d762 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7905 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7906 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7908 (p : Pattern) (guard : d1293 p = 1) : d701 p ≤ (0 : Int) + d763 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d701, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7886 p hg
    simpa only [d701, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d701, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d701, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7909 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d702, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7892 p hg
    simpa only [d702, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d702, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7908 p hg
    simpa only [d702, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7910 (p : Pattern) (guard : d1293 p = 1) : d701 p ≤ (0 : Int) + d765 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d701, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7895 p hg
    simpa only [d701, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d701, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d701, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7911 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d766 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d702, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7898 p hg
    simpa only [d702, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d702, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7910 p hg
    simpa only [d702, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7912 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d767 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7909 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7911 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7913 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d768 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7909 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7912 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7914 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d769 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7912 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7911 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7915 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d770 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7913 p hg
    simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7914 p hg
    simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7916 (p : Pattern) (guard : d1293 p = 1) : d703 p ≤ (0 : Int) + d771 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d703, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7907 p hg
    simpa only [d703, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d703, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7915 p hg
    simpa only [d703, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7917 (p : Pattern) (guard : d1293 p = 1) : d704 p ≤ (0 : Int) + d772 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d704, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7903 p hg
    simpa only [d704, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d704, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7916 p hg
    simpa only [d704, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7918 (p : Pattern) (guard : d1293 p = 1) : d705 p ≤ (0 : Int) + d773 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d705, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7897 p hg
    simpa only [d705, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d705, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d705, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7919 (p : Pattern) (guard : d1293 p = 1) : d706 p ≤ (0 : Int) + d774 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d706, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7897 p hg
    simpa only [d706, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d706, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d706, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7920 (p : Pattern) (guard : d1293 p = 1) : d707 p ≤ (0 : Int) + d775 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d707, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7900 p hg
    simpa only [d707, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d707, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7919 p hg
    simpa only [d707, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7921 (p : Pattern) (guard : d1293 p = 1) : d708 p ≤ (0 : Int) + d776 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d708, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7901 p hg
    simpa only [d708, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d708, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7920 p hg
    simpa only [d708, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7922 (p : Pattern) (guard : d1293 p = 1) : d709 p ≤ (0 : Int) + d777 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d709, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7900 p hg
    simpa only [d709, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d709, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d709, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7923 (p : Pattern) (guard : d1293 p = 1) : d710 p ≤ (0 : Int) + d778 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d710, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7901 p hg
    simpa only [d710, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d710, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7922 p hg
    simpa only [d710, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7924 (p : Pattern) (guard : d1293 p = 1) : d711 p ≤ (0 : Int) + d779 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d711, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7921 p hg
    simpa only [d711, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d711, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7923 p hg
    simpa only [d711, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7925 (p : Pattern) (guard : d1293 p = 1) : d712 p ≤ (0 : Int) + d780 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d712, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7904 p hg
    simpa only [d712, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d712, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d712, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7926 (p : Pattern) (guard : d1293 p = 1) : d713 p ≤ (0 : Int) + d781 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d713, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7905 p hg
    simpa only [d713, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d713, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7925 p hg
    simpa only [d713, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7927 (p : Pattern) (guard : d1293 p = 1) : d714 p ≤ (0 : Int) + d782 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d714, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7912 p hg
    simpa only [d714, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d714, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d714, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7928 (p : Pattern) (guard : d1293 p = 1) : d715 p ≤ (0 : Int) + d783 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d715, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7913 p hg
    simpa only [d715, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d715, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7927 p hg
    simpa only [d715, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7929 (p : Pattern) (guard : d1293 p = 1) : d716 p ≤ (0 : Int) + d784 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d716, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7926 p hg
    simpa only [d716, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d716, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7928 p hg
    simpa only [d716, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7930 (p : Pattern) (guard : d1293 p = 1) : d717 p ≤ (0 : Int) + d785 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d717, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7924 p hg
    simpa only [d717, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d717, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7929 p hg
    simpa only [d717, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7931 (p : Pattern) (guard : d1293 p = 1) : d718 p ≤ (0 : Int) + d786 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d718, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7917 p hg
    simpa only [d718, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d718, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7930 p hg
    simpa only [d718, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7932 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d787 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d719, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7886 p hg
    simpa only [d719, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d719, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7908 p hg
    simpa only [d719, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7933 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d788 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d719, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7895 p hg
    simpa only [d719, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d719, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7910 p hg
    simpa only [d719, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7934 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d789 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7932 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7935 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d790 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7932 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7936 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d791 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7937 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d792 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7938 (p : Pattern) (guard : d1293 p = 1) : d720 p ≤ (0 : Int) + d793 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d720, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7903 p hg
    simpa only [d720, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d720, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d720, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7939 (p : Pattern) (guard : d1293 p = 1) : d705 p ≤ (0 : Int) + d794 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d705, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7891 p hg
    simpa only [d705, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d705, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d705, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7940 (p : Pattern) (guard : d1293 p = 1) : d706 p ≤ (0 : Int) + d795 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d706, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7891 p hg
    simpa only [d706, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d706, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7939 p hg
    simpa only [d706, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7941 (p : Pattern) (guard : d1293 p = 1) : d706 p ≤ (0 : Int) + d796 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7940 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7919 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7942 (p : Pattern) (guard : d1293 p = 1) : d706 p ≤ (0 : Int) + d797 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7940 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7941 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7943 (p : Pattern) (guard : d1293 p = 1) : d706 p ≤ (0 : Int) + d798 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7941 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7919 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7944 (p : Pattern) (guard : d1293 p = 1) : d706 p ≤ (0 : Int) + d799 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7943 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7945 (p : Pattern) (guard : d1293 p = 1) : d721 p ≤ (0 : Int) + d800 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d721, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d721, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d721, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7944 p hg
    simpa only [d721, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7946 (p : Pattern) (guard : d1293 p = 1) : d722 p ≤ (0 : Int) + d801 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d722, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d722, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d722, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d722, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7947 (p : Pattern) (guard : d1293 p = 1) : d723 p ≤ (0 : Int) + d802 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d723, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d723, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d723, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7946 p hg
    simpa only [d723, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7948 (p : Pattern) (guard : d1293 p = 1) : d724 p ≤ (0 : Int) + d803 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d724, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7923 p hg
    simpa only [d724, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d724, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7947 p hg
    simpa only [d724, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7949 (p : Pattern) (guard : d1293 p = 1) : d725 p ≤ (0 : Int) + d804 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d725, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7941 p hg
    simpa only [d725, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d725, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d725, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7950 (p : Pattern) (guard : d1293 p = 1) : d726 p ≤ (0 : Int) + d805 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d726, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d726, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d726, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7949 p hg
    simpa only [d726, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7951 (p : Pattern) (guard : d1293 p = 1) : d705 p ≤ (0 : Int) + d806 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7939 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7952 (p : Pattern) (guard : d1293 p = 1) : d705 p ≤ (0 : Int) + d807 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7939 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7951 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7953 (p : Pattern) (guard : d1293 p = 1) : d727 p ≤ (0 : Int) + d808 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d727, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7951 p hg
    simpa only [d727, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d727, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d727, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7954 (p : Pattern) (guard : d1293 p = 1) : d728 p ≤ (0 : Int) + d809 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d728, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7952 p hg
    simpa only [d728, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d728, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7953 p hg
    simpa only [d728, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7955 (p : Pattern) (guard : d1293 p = 1) : d729 p ≤ (0 : Int) + d810 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d729, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d729, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d729, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d729, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7956 (p : Pattern) (guard : d1293 p = 1) : d730 p ≤ (0 : Int) + d811 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d730, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7948 p hg
    simpa only [d730, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d730, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7955 p hg
    simpa only [d730, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7957 (p : Pattern) (guard : d1293 p = 1) : d731 p ≤ (0 : Int) + d812 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d731, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7945 p hg
    simpa only [d731, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d731, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d731, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7958 (p : Pattern) (guard : d1293 p = 1) : d732 p ≤ (0 : Int) + d813 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d732, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7931 p hg
    simpa only [d732, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d732, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7957 p hg
    simpa only [d732, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7959 (p : Pattern) (guard : d1293 p = 1) : d733 p ≤ (0 : Int) + d814 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d733, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7923 p hg
    simpa only [d733, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d733, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7929 p hg
    simpa only [d733, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7960 (p : Pattern) (guard : d1293 p = 1) : d734 p ≤ (0 : Int) + d815 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d734, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7917 p hg
    simpa only [d734, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d734, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d734, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7961 (p : Pattern) (guard : d1293 p = 1) : d705 p ≤ (0 : Int) + d816 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7951 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7962 (p : Pattern) (guard : d1293 p = 1) : d705 p ≤ (0 : Int) + d817 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7952 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7963 (p : Pattern) (guard : d1293 p = 1) : d735 p ≤ (0 : Int) + d818 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d735, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7944 p hg
    simpa only [d735, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d735, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7962 p hg
    simpa only [d735, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7964 (p : Pattern) (guard : d1293 p = 1) : d736 p ≤ (0 : Int) + d819 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d736, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d736, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d736, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7963 p hg
    simpa only [d736, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7965 (p : Pattern) (guard : d1293 p = 1) : d737 p ≤ (0 : Int) + d820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d737, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7923 p hg
    simpa only [d737, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d737, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7928 p hg
    simpa only [d737, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7966 (p : Pattern) (guard : d1293 p = 1) : d738 p ≤ (0 : Int) + d821 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d738, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d738, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d738, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d738, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7967 (p : Pattern) (guard : d1293 p = 1) : d739 p ≤ (0 : Int) + d822 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d739, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7965 p hg
    simpa only [d739, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d739, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7966 p hg
    simpa only [d739, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7968 (p : Pattern) (guard : d1293 p = 1) : d740 p ≤ (0 : Int) + d823 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d740, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7964 p hg
    simpa only [d740, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d740, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d740, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7969 (p : Pattern) (guard : d1293 p = 1) : d741 p ≤ (0 : Int) + d824 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d741, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7960 p hg
    simpa only [d741, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d741, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7968 p hg
    simpa only [d741, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7970 (p : Pattern) (guard : d1293 p = 1) : d742 p ≤ (0 : Int) + d825 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d742, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7958 p hg
    simpa only [d742, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d742, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7969 p hg
    simpa only [d742, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7971 (p : Pattern) (guard : d29 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare7972 (p : Pattern) (guard : d1690 p = 1) : d5 p ≤ (0 : Int) + d0 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d1690, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4484 p hg
    simpa only [d1690, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7973 (p : Pattern) (guard : d1690 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare7974 (p : Pattern) (guard : d1690 p = 1) : d5 p ≤ (0 : Int) + d1691 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7972 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7973 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7975 (p : Pattern) (guard : d1690 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare7976 (p : Pattern) (guard : d1690 p = 1) : d37 p ≤ (0 : Int) + d1554 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d37, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7972 p hg
    simpa only [d37, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d37, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d37, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7977 (p : Pattern) (guard : d1690 p = 1) : d697 p ≤ (0 : Int) + d1692 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d697, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7974 p hg
    simpa only [d697, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d697, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7976 p hg
    simpa only [d697, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7978 (p : Pattern) (guard : d29 p = 1) : d1 p ≤ (0 : Int) + d1 p := by
  omega
theorem compare7979 (p : Pattern) (guard : d1690 p = 1) : d11 p ≤ (0 : Int) + d1 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7978 p hg
    simpa only [d1690, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4490 p hg
    simpa only [d1690, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
