/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5880 (p : Pattern) (guard : d0 p = 1) : d391 p ≤ (0 : Int) + d800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5881 (p : Pattern) (guard : d4301 p = 1) : d711 p ≤ (0 : Int) + d801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d711, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3206 p hg
    simpa only [d4301, d711, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d711, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5880 p hg
    simpa only [d4301, d711, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5882 (p : Pattern) (guard : d4301 p = 1) : d712 p ≤ (0 : Int) + d802 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d712, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5879 p hg
    simpa only [d712, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d712, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5881 p hg
    simpa only [d712, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5883 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5884 (p : Pattern) (guard : d4301 p = 1) : d713 p ≤ (0 : Int) + d806 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d713, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3254 p hg
    simpa only [d4301, d713, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d713, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5883 p hg
    simpa only [d4301, d713, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5885 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d811 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5886 (p : Pattern) (guard : d4301 p = 1) : d714 p ≤ (0 : Int) + d812 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d714, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3238 p hg
    simpa only [d4301, d714, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d714, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5885 p hg
    simpa only [d4301, d714, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5887 (p : Pattern) (guard : d4301 p = 1) : d715 p ≤ (0 : Int) + d813 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d715, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5884 p hg
    simpa only [d715, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d715, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5886 p hg
    simpa only [d715, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5888 (p : Pattern) (guard : d4301 p = 1) : d716 p ≤ (0 : Int) + d814 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d716, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5882 p hg
    simpa only [d716, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d716, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5887 p hg
    simpa only [d716, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5889 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5890 (p : Pattern) (guard : d4301 p = 1) : d717 p ≤ (0 : Int) + d816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d717, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3213 p hg
    simpa only [d4301, d717, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d717, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5889 p hg
    simpa only [d4301, d717, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5891 (p : Pattern) (guard : d4301 p = 1) : d714 p ≤ (0 : Int) + d818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d714, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3217 p hg
    simpa only [d4301, d714, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d714, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5885 p hg
    simpa only [d4301, d714, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5892 (p : Pattern) (guard : d4301 p = 1) : d718 p ≤ (0 : Int) + d819 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d718, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5890 p hg
    simpa only [d718, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d718, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5891 p hg
    simpa only [d718, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5893 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (0 : Int) + d90 p := by
  omega
theorem compare5894 (p : Pattern) (guard : d0 p = 1) : d91 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5895 (p : Pattern) (guard : d4299 p = 1) : d92 p ≤ (0 : Int) + d820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d92, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5893 p hg
    simpa only [d4299, d92, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d92, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5894 p hg
    simpa only [d4299, d92, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5896 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d93 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5897 (p : Pattern) (guard : d4301 p = 1) : d719 p ≤ (0 : Int) + d821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d719, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5895 p hg
    simpa only [d4301, d719, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d719, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d4301, d719, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5898 (p : Pattern) (guard : d4301 p = 1) : d95 p ≤ (0 : Int) + d95 p := by
  omega
theorem compare5899 (p : Pattern) (guard : d4301 p = 1) : d720 p ≤ (0 : Int) + d822 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d720, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5897 p hg
    simpa only [d720, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d720, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d720, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5900 (p : Pattern) (guard : d4301 p = 1) : d721 p ≤ (0 : Int) + d823 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d721, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5892 p hg
    simpa only [d721, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d721, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5899 p hg
    simpa only [d721, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5901 (p : Pattern) (guard : d4301 p = 1) : d722 p ≤ (0 : Int) + d824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d722, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5888 p hg
    simpa only [d722, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d722, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5900 p hg
    simpa only [d722, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5902 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d826 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5903 (p : Pattern) (guard : d4301 p = 1) : d723 p ≤ (0 : Int) + d827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d723, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3225 p hg
    simpa only [d4301, d723, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d723, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5902 p hg
    simpa only [d4301, d723, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5904 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5905 (p : Pattern) (guard : d4301 p = 1) : d724 p ≤ (0 : Int) + d829 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d724, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3229 p hg
    simpa only [d4301, d724, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d724, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5904 p hg
    simpa only [d4301, d724, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5906 (p : Pattern) (guard : d4301 p = 1) : d725 p ≤ (0 : Int) + d830 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d725, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5903 p hg
    simpa only [d725, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d725, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5905 p hg
    simpa only [d725, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5907 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5908 (p : Pattern) (guard : d4301 p = 1) : d726 p ≤ (0 : Int) + d832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d726, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3235 p hg
    simpa only [d4301, d726, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d726, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5907 p hg
    simpa only [d4301, d726, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5909 (p : Pattern) (guard : d4301 p = 1) : d727 p ≤ (0 : Int) + d833 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d727, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5908 p hg
    simpa only [d727, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d727, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5886 p hg
    simpa only [d727, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5910 (p : Pattern) (guard : d4301 p = 1) : d728 p ≤ (0 : Int) + d834 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d728, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d728, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d728, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d728, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5911 (p : Pattern) (guard : d4301 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare5912 (p : Pattern) (guard : d4301 p = 1) : d729 p ≤ (0 : Int) + d835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d729, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d729, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d729, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d729, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5913 (p : Pattern) (guard : d4301 p = 1) : d730 p ≤ (0 : Int) + d836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d730, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5910 p hg
    simpa only [d730, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d730, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5912 p hg
    simpa only [d730, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5914 (p : Pattern) (guard : d4301 p = 1) : d731 p ≤ (0 : Int) + d837 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d731, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5901 p hg
    simpa only [d731, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d731, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5913 p hg
    simpa only [d731, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5915 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d826 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5916 (p : Pattern) (guard : d4301 p = 1) : d732 p ≤ (0 : Int) + d839 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d732, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3245 p hg
    simpa only [d4301, d732, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d732, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5915 p hg
    simpa only [d4301, d732, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5917 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5918 (p : Pattern) (guard : d4301 p = 1) : d733 p ≤ (0 : Int) + d841 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d733, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3248 p hg
    simpa only [d4301, d733, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d733, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5917 p hg
    simpa only [d4301, d733, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5919 (p : Pattern) (guard : d4301 p = 1) : d734 p ≤ (0 : Int) + d842 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d734, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5916 p hg
    simpa only [d734, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d734, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5918 p hg
    simpa only [d734, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5920 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5921 (p : Pattern) (guard : d4299 p = 1) : d29 p ≤ (0 : Int) + d843 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d29, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d29, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d29, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d4299, d29, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5922 (p : Pattern) (guard : d4301 p = 1) : d726 p ≤ (0 : Int) + d844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d726, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5921 p hg
    simpa only [d4301, d726, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d726, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5907 p hg
    simpa only [d4301, d726, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5923 (p : Pattern) (guard : d4301 p = 1) : d727 p ≤ (0 : Int) + d845 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d727, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5922 p hg
    simpa only [d727, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d727, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5886 p hg
    simpa only [d727, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5924 (p : Pattern) (guard : d4301 p = 1) : d735 p ≤ (0 : Int) + d846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d735, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5919 p hg
    simpa only [d735, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d735, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5923 p hg
    simpa only [d735, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5925 (p : Pattern) (guard : d4301 p = 1) : d736 p ≤ (0 : Int) + d847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d736, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5887 p hg
    simpa only [d736, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d736, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5899 p hg
    simpa only [d736, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5926 (p : Pattern) (guard : d4301 p = 1) : d737 p ≤ (0 : Int) + d848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d737, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5924 p hg
    simpa only [d737, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d737, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5925 p hg
    simpa only [d737, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5927 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d826 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5928 (p : Pattern) (guard : d4301 p = 1) : d717 p ≤ (0 : Int) + d849 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d717, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3213 p hg
    simpa only [d4301, d717, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d717, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5927 p hg
    simpa only [d4301, d717, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5929 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5930 (p : Pattern) (guard : d4301 p = 1) : d714 p ≤ (0 : Int) + d850 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d714, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3217 p hg
    simpa only [d4301, d714, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d714, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5929 p hg
    simpa only [d4301, d714, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5931 (p : Pattern) (guard : d4301 p = 1) : d718 p ≤ (0 : Int) + d851 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d718, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5928 p hg
    simpa only [d718, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d718, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5930 p hg
    simpa only [d718, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5932 (p : Pattern) (guard : d4301 p = 1) : d738 p ≤ (0 : Int) + d852 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d738, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5931 p hg
    simpa only [d738, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d738, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d738, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5933 (p : Pattern) (guard : d4301 p = 1) : d739 p ≤ (0 : Int) + d853 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d739, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5932 p hg
    simpa only [d739, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d739, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5912 p hg
    simpa only [d739, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5934 (p : Pattern) (guard : d4301 p = 1) : d740 p ≤ (0 : Int) + d854 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d740, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5926 p hg
    simpa only [d740, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d740, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5933 p hg
    simpa only [d740, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5935 (p : Pattern) (guard : d4301 p = 1) : d741 p ≤ (0 : Int) + d855 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d741, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5914 p hg
    simpa only [d741, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d741, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5934 p hg
    simpa only [d741, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5936 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d858 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5937 (p : Pattern) (guard : d4301 p = 1) : d742 p ≤ (0 : Int) + d859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d742, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3270 p hg
    simpa only [d4301, d742, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d742, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5936 p hg
    simpa only [d4301, d742, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5938 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5939 (p : Pattern) (guard : d4301 p = 1) : d743 p ≤ (0 : Int) + d866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d743, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3275 p hg
    simpa only [d4301, d743, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d743, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5938 p hg
    simpa only [d4301, d743, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5940 (p : Pattern) (guard : d4301 p = 1) : d744 p ≤ (0 : Int) + d867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d744, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5937 p hg
    simpa only [d744, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d744, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5939 p hg
    simpa only [d744, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5941 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5942 (p : Pattern) (guard : d4299 p = 1) : d114 p ≤ (0 : Int) + d868 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d114, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d114, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d114, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5941 p hg
    simpa only [d4299, d114, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5943 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d870 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5944 (p : Pattern) (guard : d4301 p = 1) : d745 p ≤ (0 : Int) + d871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d745, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5942 p hg
    simpa only [d4301, d745, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d745, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5943 p hg
    simpa only [d4301, d745, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5945 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5946 (p : Pattern) (guard : d4301 p = 1) : d746 p ≤ (0 : Int) + d876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d746, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3286 p hg
    simpa only [d4301, d746, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d746, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5945 p hg
    simpa only [d4301, d746, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5947 (p : Pattern) (guard : d4301 p = 1) : d747 p ≤ (0 : Int) + d877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d747, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5944 p hg
    simpa only [d747, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d747, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d747, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5948 (p : Pattern) (guard : d4301 p = 1) : d748 p ≤ (0 : Int) + d878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d748, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5940 p hg
    simpa only [d748, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d748, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5947 p hg
    simpa only [d748, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5949 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d870 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5950 (p : Pattern) (guard : d4301 p = 1) : d749 p ≤ (0 : Int) + d880 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d749, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3282 p hg
    simpa only [d4301, d749, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d749, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5949 p hg
    simpa only [d4301, d749, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5951 (p : Pattern) (guard : d4301 p = 1) : d750 p ≤ (0 : Int) + d881 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d750, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5950 p hg
    simpa only [d750, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d750, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d750, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5952 (p : Pattern) (guard : d4301 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare5953 (p : Pattern) (guard : d4301 p = 1) : d751 p ≤ (0 : Int) + d882 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d751, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5951 p hg
    simpa only [d751, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d751, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5952 p hg
    simpa only [d751, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5954 (p : Pattern) (guard : d4301 p = 1) : d752 p ≤ (0 : Int) + d883 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d752, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5948 p hg
    simpa only [d752, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d752, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5953 p hg
    simpa only [d752, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5955 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d858 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5956 (p : Pattern) (guard : d4301 p = 1) : d753 p ≤ (0 : Int) + d885 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d753, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3293 p hg
    simpa only [d4301, d753, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d753, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5955 p hg
    simpa only [d4301, d753, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5957 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5958 (p : Pattern) (guard : d4301 p = 1) : d746 p ≤ (0 : Int) + d887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d746, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d4301, d746, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d746, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5957 p hg
    simpa only [d4301, d746, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5959 (p : Pattern) (guard : d4301 p = 1) : d754 p ≤ (0 : Int) + d888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d754, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5956 p hg
    simpa only [d754, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d754, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5958 p hg
    simpa only [d754, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5960 (p : Pattern) (guard : d4301 p = 1) : d745 p ≤ (0 : Int) + d890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d745, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3302 p hg
    simpa only [d4301, d745, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d745, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5943 p hg
    simpa only [d4301, d745, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5961 (p : Pattern) (guard : d4301 p = 1) : d747 p ≤ (0 : Int) + d891 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d747, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5960 p hg
    simpa only [d747, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d747, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d747, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5962 (p : Pattern) (guard : d4301 p = 1) : d755 p ≤ (0 : Int) + d892 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d755, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5959 p hg
    simpa only [d755, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d755, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5961 p hg
    simpa only [d755, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5963 (p : Pattern) (guard : d4301 p = 1) : d756 p ≤ (0 : Int) + d893 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d756, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5961 p hg
    simpa only [d756, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d756, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d756, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5964 (p : Pattern) (guard : d4301 p = 1) : d757 p ≤ (0 : Int) + d894 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d757, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5962 p hg
    simpa only [d757, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d757, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5963 p hg
    simpa only [d757, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5965 (p : Pattern) (guard : d4301 p = 1) : d758 p ≤ (0 : Int) + d895 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d758, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5954 p hg
    simpa only [d758, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d758, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5964 p hg
    simpa only [d758, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5966 (p : Pattern) (guard : d4301 p = 1) : d759 p ≤ (0 : Int) + d896 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d759, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5914 p hg
    simpa only [d759, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d759, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5965 p hg
    simpa only [d759, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5967 (p : Pattern) (guard : d4301 p = 1) : d760 p ≤ (0 : Int) + d897 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d760, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5935 p hg
    simpa only [d760, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d760, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5966 p hg
    simpa only [d760, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5968 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d900 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5969 (p : Pattern) (guard : d4301 p = 1) : d761 p ≤ (0 : Int) + d901 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d761, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3314 p hg
    simpa only [d4301, d761, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d761, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5968 p hg
    simpa only [d4301, d761, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5970 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d904 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5971 (p : Pattern) (guard : d4301 p = 1) : d762 p ≤ (0 : Int) + d905 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d762, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3319 p hg
    simpa only [d4301, d762, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d762, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5970 p hg
    simpa only [d4301, d762, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5972 (p : Pattern) (guard : d4301 p = 1) : d763 p ≤ (0 : Int) + d906 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d763, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5969 p hg
    simpa only [d763, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d763, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5971 p hg
    simpa only [d763, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5973 (p : Pattern) (guard : d4301 p = 1) : d764 p ≤ (0 : Int) + d907 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d764, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5931 p hg
    simpa only [d764, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d764, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5972 p hg
    simpa only [d764, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5974 (p : Pattern) (guard : d4301 p = 1) : d765 p ≤ (0 : Int) + d908 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d765, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5972 p hg
    simpa only [d765, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d765, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d765, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5975 (p : Pattern) (guard : d4301 p = 1) : d766 p ≤ (0 : Int) + d909 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d766, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5973 p hg
    simpa only [d766, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d766, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5974 p hg
    simpa only [d766, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5976 (p : Pattern) (guard : d4301 p = 1) : d767 p ≤ (0 : Int) + d910 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d767, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5926 p hg
    simpa only [d767, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d767, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5975 p hg
    simpa only [d767, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5977 (p : Pattern) (guard : d4301 p = 1) : d768 p ≤ (0 : Int) + d911 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d768, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5914 p hg
    simpa only [d768, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d768, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5976 p hg
    simpa only [d768, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5978 (p : Pattern) (guard : d4301 p = 1) : d769 p ≤ (0 : Int) + d913 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d769, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3329 p hg
    simpa only [d4301, d769, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d769, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5938 p hg
    simpa only [d4301, d769, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5979 (p : Pattern) (guard : d4301 p = 1) : d770 p ≤ (0 : Int) + d914 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d770, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5937 p hg
    simpa only [d770, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d770, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5978 p hg
    simpa only [d770, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5980 (p : Pattern) (guard : d4301 p = 1) : d771 p ≤ (0 : Int) + d916 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d771, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3336 p hg
    simpa only [d4301, d771, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d771, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5945 p hg
    simpa only [d4301, d771, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5981 (p : Pattern) (guard : d4301 p = 1) : d772 p ≤ (0 : Int) + d917 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d772, d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5944 p hg
    simpa only [d772, d917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d772, d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d772, d917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5982 (p : Pattern) (guard : d4301 p = 1) : d773 p ≤ (0 : Int) + d918 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d773, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5979 p hg
    simpa only [d773, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d773, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5981 p hg
    simpa only [d773, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5983 (p : Pattern) (guard : d4301 p = 1) : d774 p ≤ (0 : Int) + d919 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d774, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5950 p hg
    simpa only [d774, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d774, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d774, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5984 (p : Pattern) (guard : d4301 p = 1) : d775 p ≤ (0 : Int) + d920 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d775, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5983 p hg
    simpa only [d775, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d775, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5952 p hg
    simpa only [d775, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5985 (p : Pattern) (guard : d4301 p = 1) : d776 p ≤ (0 : Int) + d921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d776, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5982 p hg
    simpa only [d776, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d776, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5984 p hg
    simpa only [d776, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5986 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d923 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5987 (p : Pattern) (guard : d4301 p = 1) : d753 p ≤ (0 : Int) + d924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d753, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3293 p hg
    simpa only [d4301, d753, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d753, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5986 p hg
    simpa only [d4301, d753, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5988 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d927 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5989 (p : Pattern) (guard : d4301 p = 1) : d771 p ≤ (0 : Int) + d928 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d771, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3336 p hg
    simpa only [d4301, d771, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d771, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5988 p hg
    simpa only [d4301, d771, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5990 (p : Pattern) (guard : d4301 p = 1) : d777 p ≤ (0 : Int) + d929 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d777, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5987 p hg
    simpa only [d777, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d777, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d777, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5991 (p : Pattern) (guard : d1 p = 1) : d242 p ≤ (0 : Int) + d242 p := by
  omega
theorem compare5992 (p : Pattern) (guard : d4299 p = 1) : d243 p ≤ (0 : Int) + d930 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d243, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5991 p hg
    simpa only [d4299, d243, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d243, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3285 p hg
    simpa only [d4299, d243, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5993 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d931 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5994 (p : Pattern) (guard : d4301 p = 1) : d778 p ≤ (0 : Int) + d932 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d778, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5992 p hg
    simpa only [d4301, d778, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d778, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5993 p hg
    simpa only [d4301, d778, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5995 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d934 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5996 (p : Pattern) (guard : d4301 p = 1) : d779 p ≤ (0 : Int) + d935 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d779, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3356 p hg
    simpa only [d4301, d779, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d779, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5995 p hg
    simpa only [d4301, d779, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5997 (p : Pattern) (guard : d4301 p = 1) : d780 p ≤ (0 : Int) + d936 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d780, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5994 p hg
    simpa only [d780, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d780, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5996 p hg
    simpa only [d780, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5998 (p : Pattern) (guard : d4301 p = 1) : d781 p ≤ (0 : Int) + d937 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d781, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5990 p hg
    simpa only [d781, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d781, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5997 p hg
    simpa only [d781, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5999 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6000 (p : Pattern) (guard : d4301 p = 1) : d782 p ≤ (0 : Int) + d941 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d782, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3351 p hg
    simpa only [d4301, d782, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d782, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5999 p hg
    simpa only [d4301, d782, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6001 (p : Pattern) (guard : d4301 p = 1) : d783 p ≤ (0 : Int) + d942 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d783, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6000 p hg
    simpa only [d783, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d783, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5996 p hg
    simpa only [d783, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6002 (p : Pattern) (guard : d4301 p = 1) : d784 p ≤ (0 : Int) + d943 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d784, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6001 p hg
    simpa only [d784, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d784, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d784, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6003 (p : Pattern) (guard : d4301 p = 1) : d785 p ≤ (0 : Int) + d944 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d785, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5998 p hg
    simpa only [d785, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d785, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d785, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6004 (p : Pattern) (guard : d4301 p = 1) : d786 p ≤ (0 : Int) + d945 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d786, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5985 p hg
    simpa only [d786, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d786, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6003 p hg
    simpa only [d786, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6005 (p : Pattern) (guard : d4301 p = 1) : d787 p ≤ (0 : Int) + d946 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d787, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5914 p hg
    simpa only [d787, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d787, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6004 p hg
    simpa only [d787, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6006 (p : Pattern) (guard : d4301 p = 1) : d788 p ≤ (0 : Int) + d947 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d788, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5977 p hg
    simpa only [d788, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d788, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6005 p hg
    simpa only [d788, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6007 (p : Pattern) (guard : d4301 p = 1) : d789 p ≤ (0 : Int) + d948 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d789, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5967 p hg
    simpa only [d789, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d789, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6006 p hg
    simpa only [d789, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6008 (p : Pattern) (guard : d0 p = 1) : d22 p ≤ (2 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6009 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (2 : Int) + d21 p := by
  omega
theorem compare6010 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (2 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6011 (p : Pattern) (guard : d4395 p = 1) : d28 p ≤ (2 : Int) + d21 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6009 p hg
    simpa only [d4395, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6010 p hg
    simpa only [d4395, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6012 (p : Pattern) (guard : d4617 p = 1) : d29 p ≤ (2 : Int) + d21 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6008 p hg
    simpa only [d4617, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6011 p hg
    simpa only [d4617, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6013 (p : Pattern) (guard : d0 p = 1) : d376 p ≤ (2 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6014 (p : Pattern) (guard : d4618 p = 1) : d710 p ≤ (2 : Int) + d4619 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d710, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d4618, d710, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d710, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6013 p hg
    simpa only [d4618, d710, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6015 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (2 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6016 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d20 p := by
  omega
theorem compare6017 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d9 p := by
  change (10 : Int) ≤ (2 : Int) + 9
  decide
theorem compare6018 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6017 p hg
    simpa only [d57, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d57, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6019 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6017 p hg
    simpa only [d58, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6018 p hg
    simpa only [d58, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
