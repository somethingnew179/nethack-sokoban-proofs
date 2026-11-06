/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5880 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (1 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5865 p hg
    simpa only [d119, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5870 p hg
    simpa only [d119, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5881 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (1 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5865 p hg
    simpa only [d120, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5880 p hg
    simpa only [d120, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5882 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (1 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5883 (p : Pattern) (guard : d770 p = 1) : d127 p ≤ (1 : Int) + d126 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5881 p hg
    simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5882 p hg
    simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5884 (p : Pattern) (guard : d770 p = 1) : d128 p ≤ (1 : Int) + d1101 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d128, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5883 p hg
    simpa only [d128, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d128, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d128, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5885 (p : Pattern) (guard : d770 p = 1) : d129 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d129, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5879 p hg
    simpa only [d129, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d129, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5884 p hg
    simpa only [d129, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5886 (p : Pattern) (guard : d770 p = 1) : d237 p ≤ (1 : Int) + d1103 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d237, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5879 p hg
    simpa only [d237, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d237, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5885 p hg
    simpa only [d237, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5887 (p : Pattern) (guard : d770 p = 1) : d238 p ≤ (1 : Int) + d1104 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d238, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5876 p hg
    simpa only [d238, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d238, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5886 p hg
    simpa only [d238, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5888 (p : Pattern) (guard : d770 p = 1) : d239 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d239, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5875 p hg
    simpa only [d239, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d239, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5887 p hg
    simpa only [d239, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5889 (p : Pattern) (guard : d770 p = 1) : d68 p ≤ (1 : Int) + d68 p := by
  omega
theorem compare5890 (p : Pattern) (guard : d770 p = 1) : d69 p ≤ (1 : Int) + d1106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d69, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5874 p hg
    simpa only [d69, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d69, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d69, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5891 (p : Pattern) (guard : d770 p = 1) : d70 p ≤ (1 : Int) + d1107 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d70, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5889 p hg
    simpa only [d70, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d70, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5890 p hg
    simpa only [d70, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5892 (p : Pattern) (guard : d770 p = 1) : d181 p ≤ (1 : Int) + d181 p := by
  omega
theorem compare5893 (p : Pattern) (guard : d770 p = 1) : d240 p ≤ (1 : Int) + d1108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d240, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5885 p hg
    simpa only [d240, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d240, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d240, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5894 (p : Pattern) (guard : d770 p = 1) : d241 p ≤ (1 : Int) + d1109 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d241, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5892 p hg
    simpa only [d241, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d241, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5893 p hg
    simpa only [d241, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5895 (p : Pattern) (guard : d770 p = 1) : d242 p ≤ (1 : Int) + d1110 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d242, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5891 p hg
    simpa only [d242, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d242, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5894 p hg
    simpa only [d242, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5896 (p : Pattern) (guard : d770 p = 1) : d243 p ≤ (1 : Int) + d1111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d243, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5888 p hg
    simpa only [d243, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d243, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5895 p hg
    simpa only [d243, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5897 (p : Pattern) (guard : d770 p = 1) : d55 p ≤ (1 : Int) + d55 p := by
  omega
theorem compare5898 (p : Pattern) (guard : d770 p = 1) : d66 p ≤ (1 : Int) + d1112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d66, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5897 p hg
    simpa only [d66, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d66, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d66, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5899 (p : Pattern) (guard : d770 p = 1) : d244 p ≤ (1 : Int) + d1113 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d244, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5895 p hg
    simpa only [d244, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d244, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d244, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5900 (p : Pattern) (guard : d770 p = 1) : d245 p ≤ (1 : Int) + d1114 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d245, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d245, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d245, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5899 p hg
    simpa only [d245, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5901 (p : Pattern) (guard : d770 p = 1) : d186 p ≤ (1 : Int) + d186 p := by
  omega
theorem compare5902 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (1 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5880 p hg
    simpa only [d137, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5870 p hg
    simpa only [d137, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5903 (p : Pattern) (guard : d0 p = 1) : d143 p ≤ (1 : Int) + d143 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5904 (p : Pattern) (guard : d770 p = 1) : d144 p ≤ (1 : Int) + d143 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5902 p hg
    simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5903 p hg
    simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5905 (p : Pattern) (guard : d770 p = 1) : d146 p ≤ (1 : Int) + d1115 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d146, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5883 p hg
    simpa only [d146, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d146, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5904 p hg
    simpa only [d146, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5906 (p : Pattern) (guard : d770 p = 1) : d155 p ≤ (1 : Int) + d1116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d155, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5874 p hg
    simpa only [d155, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d155, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5905 p hg
    simpa only [d155, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5907 (p : Pattern) (guard : d770 p = 1) : d246 p ≤ (1 : Int) + d1117 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d246, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5874 p hg
    simpa only [d246, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d246, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d246, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5908 (p : Pattern) (guard : d770 p = 1) : d247 p ≤ (1 : Int) + d1118 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d247, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5901 p hg
    simpa only [d247, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d247, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5907 p hg
    simpa only [d247, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5909 (p : Pattern) (guard : d770 p = 1) : d248 p ≤ (1 : Int) + d1119 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5908 p hg
    simpa only [d248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5910 (p : Pattern) (guard : d770 p = 1) : d188 p ≤ (1 : Int) + d188 p := by
  omega
theorem compare5911 (p : Pattern) (guard : d770 p = 1) : d145 p ≤ (1 : Int) + d1120 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d145, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5867 p hg
    simpa only [d145, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d145, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5904 p hg
    simpa only [d145, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5912 (p : Pattern) (guard : d770 p = 1) : d147 p ≤ (1 : Int) + d1121 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d147, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d147, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d147, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5905 p hg
    simpa only [d147, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5913 (p : Pattern) (guard : d770 p = 1) : d249 p ≤ (1 : Int) + d1122 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d249, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5912 p hg
    simpa only [d249, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d249, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d249, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5914 (p : Pattern) (guard : d770 p = 1) : d250 p ≤ (1 : Int) + d1123 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d250, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5910 p hg
    simpa only [d250, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d250, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5913 p hg
    simpa only [d250, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5915 (p : Pattern) (guard : d770 p = 1) : d251 p ≤ (1 : Int) + d1124 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5914 p hg
    simpa only [d251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5916 (p : Pattern) (guard : d770 p = 1) : d252 p ≤ (1 : Int) + d1125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d252, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d252, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d252, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5915 p hg
    simpa only [d252, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5917 (p : Pattern) (guard : d770 p = 1) : d191 p ≤ (1 : Int) + d191 p := by
  omega
theorem compare5918 (p : Pattern) (guard : d770 p = 1) : d253 p ≤ (1 : Int) + d1126 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d253, d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d253, d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d253, d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d253, d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5919 (p : Pattern) (guard : d770 p = 1) : d254 p ≤ (1 : Int) + d1127 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d254, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5917 p hg
    simpa only [d254, d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d254, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5918 p hg
    simpa only [d254, d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5920 (p : Pattern) (guard : d770 p = 1) : d255 p ≤ (1 : Int) + d1128 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d255, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5919 p hg
    simpa only [d255, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d255, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d255, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5921 (p : Pattern) (guard : d770 p = 1) : d256 p ≤ (1 : Int) + d1129 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d256, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d256, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d256, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d256, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5922 (p : Pattern) (guard : d770 p = 1) : d257 p ≤ (1 : Int) + d1130 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d257, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5916 p hg
    simpa only [d257, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d257, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5921 p hg
    simpa only [d257, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5923 (p : Pattern) (guard : d770 p = 1) : d258 p ≤ (1 : Int) + d1131 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d258, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5900 p hg
    simpa only [d258, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d258, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5922 p hg
    simpa only [d258, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5924 (p : Pattern) (guard : d851 p = 1) : d64 p ≤ (2 : Int) + d64 p := by
  omega
theorem compare5925 (p : Pattern) (guard : d851 p = 1) : d106 p ≤ (2 : Int) + d106 p := by
  omega
theorem compare5926 (p : Pattern) (guard : d851 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  omega
theorem compare5927 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (2 : Int) + d55 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2333 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5928 (p : Pattern) (guard : d851 p = 1) : d120 p ≤ (2 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5926 p hg
    simpa only [d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5927 p hg
    simpa only [d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5929 (p : Pattern) (guard : d851 p = 1) : d121 p ≤ (2 : Int) + d452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d121, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5928 p hg
    simpa only [d121, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d121, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d121, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5930 (p : Pattern) (guard : d851 p = 1) : d122 p ≤ (2 : Int) + d1281 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d122, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5925 p hg
    simpa only [d122, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d122, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5929 p hg
    simpa only [d122, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5931 (p : Pattern) (guard : d851 p = 1) : d179 p ≤ (2 : Int) + d1282 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d179, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5925 p hg
    simpa only [d179, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d179, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5930 p hg
    simpa only [d179, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5932 (p : Pattern) (guard : d851 p = 1) : d109 p ≤ (2 : Int) + d109 p := by
  omega
theorem compare5933 (p : Pattern) (guard : d851 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  omega
theorem compare5934 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (2 : Int) + d60 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2737 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5935 (p : Pattern) (guard : d851 p = 1) : d126 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5933 p hg
    simpa only [d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5934 p hg
    simpa only [d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5936 (p : Pattern) (guard : d851 p = 1) : d127 p ≤ (2 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5928 p hg
    simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5935 p hg
    simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5937 (p : Pattern) (guard : d851 p = 1) : d128 p ≤ (2 : Int) + d453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d128, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5936 p hg
    simpa only [d128, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d128, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d128, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5938 (p : Pattern) (guard : d851 p = 1) : d129 p ≤ (2 : Int) + d1283 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d129, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5932 p hg
    simpa only [d129, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d129, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5937 p hg
    simpa only [d129, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5939 (p : Pattern) (guard : d851 p = 1) : d237 p ≤ (2 : Int) + d1284 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d237, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5932 p hg
    simpa only [d237, d1284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d237, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5938 p hg
    simpa only [d237, d1284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5940 (p : Pattern) (guard : d851 p = 1) : d238 p ≤ (2 : Int) + d1285 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d238, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5931 p hg
    simpa only [d238, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d238, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5939 p hg
    simpa only [d238, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5941 (p : Pattern) (guard : d851 p = 1) : d239 p ≤ (2 : Int) + d1286 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d239, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5924 p hg
    simpa only [d239, d1286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d239, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5940 p hg
    simpa only [d239, d1286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5942 (p : Pattern) (guard : d851 p = 1) : d70 p ≤ (2 : Int) + d70 p := by
  omega
theorem compare5943 (p : Pattern) (guard : d851 p = 1) : d181 p ≤ (2 : Int) + d1287 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d181, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5930 p hg
    simpa only [d181, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d181, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d181, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5944 (p : Pattern) (guard : d851 p = 1) : d240 p ≤ (2 : Int) + d1288 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d240, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5938 p hg
    simpa only [d240, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d240, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d240, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5945 (p : Pattern) (guard : d851 p = 1) : d241 p ≤ (2 : Int) + d1289 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d241, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5943 p hg
    simpa only [d241, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d241, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5944 p hg
    simpa only [d241, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5946 (p : Pattern) (guard : d851 p = 1) : d242 p ≤ (2 : Int) + d1290 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d242, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5942 p hg
    simpa only [d242, d1290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d242, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5945 p hg
    simpa only [d242, d1290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5947 (p : Pattern) (guard : d851 p = 1) : d243 p ≤ (2 : Int) + d1291 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d243, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5941 p hg
    simpa only [d243, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d243, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d243, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5948 (p : Pattern) (guard : d851 p = 1) : d244 p ≤ (2 : Int) + d1292 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d244, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d244, d1292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d244, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d244, d1292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5949 (p : Pattern) (guard : d851 p = 1) : d245 p ≤ (2 : Int) + d1293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d245, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5947 p hg
    simpa only [d245, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d245, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5948 p hg
    simpa only [d245, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5950 (p : Pattern) (guard : d851 p = 1) : d57 p ≤ (2 : Int) + d57 p := by
  omega
theorem compare5951 (p : Pattern) (guard : d851 p = 1) : d137 p ≤ (2 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5927 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5952 (p : Pattern) (guard : d851 p = 1) : d139 p ≤ (2 : Int) + d452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d139, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5928 p hg
    simpa only [d139, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d139, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5951 p hg
    simpa only [d139, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5953 (p : Pattern) (guard : d851 p = 1) : d153 p ≤ (2 : Int) + d1294 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d153, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5950 p hg
    simpa only [d153, d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d153, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5952 p hg
    simpa only [d153, d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5954 (p : Pattern) (guard : d851 p = 1) : d186 p ≤ (2 : Int) + d1295 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d186, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5950 p hg
    simpa only [d186, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d186, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5953 p hg
    simpa only [d186, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5955 (p : Pattern) (guard : d851 p = 1) : d63 p ≤ (2 : Int) + d63 p := by
  omega
theorem compare5956 (p : Pattern) (guard : d851 p = 1) : d143 p ≤ (2 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5934 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4262 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5957 (p : Pattern) (guard : d851 p = 1) : d144 p ≤ (2 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5951 p hg
    simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5956 p hg
    simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5958 (p : Pattern) (guard : d851 p = 1) : d146 p ≤ (2 : Int) + d453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d146, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5936 p hg
    simpa only [d146, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d146, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5957 p hg
    simpa only [d146, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5959 (p : Pattern) (guard : d851 p = 1) : d155 p ≤ (2 : Int) + d1296 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d155, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5955 p hg
    simpa only [d155, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d155, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5958 p hg
    simpa only [d155, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5960 (p : Pattern) (guard : d851 p = 1) : d246 p ≤ (2 : Int) + d1297 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d246, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5955 p hg
    simpa only [d246, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d246, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5959 p hg
    simpa only [d246, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5961 (p : Pattern) (guard : d851 p = 1) : d247 p ≤ (2 : Int) + d1298 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d247, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5954 p hg
    simpa only [d247, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d247, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5960 p hg
    simpa only [d247, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5962 (p : Pattern) (guard : d851 p = 1) : d248 p ≤ (2 : Int) + d1299 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d248, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5961 p hg
    simpa only [d248, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d248, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d248, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5963 (p : Pattern) (guard : d851 p = 1) : d138 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5926 p hg
    simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5951 p hg
    simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5964 (p : Pattern) (guard : d851 p = 1) : d140 p ≤ (2 : Int) + d1281 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d140, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5963 p hg
    simpa only [d140, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d140, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5952 p hg
    simpa only [d140, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5965 (p : Pattern) (guard : d851 p = 1) : d188 p ≤ (2 : Int) + d1287 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d188, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5964 p hg
    simpa only [d188, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d188, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d188, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5966 (p : Pattern) (guard : d851 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare5967 (p : Pattern) (guard : d851 p = 1) : d145 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5966 p hg
    simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5957 p hg
    simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5968 (p : Pattern) (guard : d851 p = 1) : d147 p ≤ (2 : Int) + d1283 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d147, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5967 p hg
    simpa only [d147, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d147, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5958 p hg
    simpa only [d147, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5969 (p : Pattern) (guard : d851 p = 1) : d249 p ≤ (2 : Int) + d1288 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d249, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5968 p hg
    simpa only [d249, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d249, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d249, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5970 (p : Pattern) (guard : d851 p = 1) : d250 p ≤ (2 : Int) + d1289 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d250, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5965 p hg
    simpa only [d250, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d250, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5969 p hg
    simpa only [d250, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5971 (p : Pattern) (guard : d851 p = 1) : d251 p ≤ (2 : Int) + d1300 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d251, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5970 p hg
    simpa only [d251, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d251, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d251, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5972 (p : Pattern) (guard : d851 p = 1) : d252 p ≤ (2 : Int) + d1301 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d252, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5962 p hg
    simpa only [d252, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d252, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5971 p hg
    simpa only [d252, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5973 (p : Pattern) (guard : d851 p = 1) : d191 p ≤ (2 : Int) + d1302 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d191, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5953 p hg
    simpa only [d191, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d191, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d191, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5974 (p : Pattern) (guard : d851 p = 1) : d253 p ≤ (2 : Int) + d1303 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d253, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5959 p hg
    simpa only [d253, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d253, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d253, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5975 (p : Pattern) (guard : d851 p = 1) : d254 p ≤ (2 : Int) + d1304 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d254, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5973 p hg
    simpa only [d254, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d254, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5974 p hg
    simpa only [d254, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5976 (p : Pattern) (guard : d851 p = 1) : d255 p ≤ (2 : Int) + d1305 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d255, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5975 p hg
    simpa only [d255, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d255, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d255, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5977 (p : Pattern) (guard : d851 p = 1) : d256 p ≤ (2 : Int) + d1306 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d256, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5976 p hg
    simpa only [d256, d1306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d256, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d256, d1306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5978 (p : Pattern) (guard : d851 p = 1) : d257 p ≤ (2 : Int) + d1307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d257, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5972 p hg
    simpa only [d257, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d257, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5977 p hg
    simpa only [d257, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5979 (p : Pattern) (guard : d851 p = 1) : d258 p ≤ (2 : Int) + d1308 p := by
  cases selected : p 108 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d258, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5949 p hg
    simpa only [d258, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d258, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5978 p hg
    simpa only [d258, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5980 (p : Pattern) (guard : d1233 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare5981 (p : Pattern) (guard : d1233 p = 1) : d0 p ≤ (0 : Int) + d35 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2784 p hg
    simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5982 (p : Pattern) (guard : d1233 p = 1) : d0 p ≤ (0 : Int) + d36 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5981 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5983 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5984 (p : Pattern) (guard : d1233 p = 1) : d0 p ≤ (0 : Int) + d16 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5983 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5985 (p : Pattern) (guard : d1233 p = 1) : d2 p ≤ (0 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5986 (p : Pattern) (guard : d1233 p = 1) : d6 p ≤ (0 : Int) + d37 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d6, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5984 p hg
    simpa only [d6, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d6, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5985 p hg
    simpa only [d6, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5987 (p : Pattern) (guard : d1233 p = 1) : d7 p ≤ (0 : Int) + d38 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d7, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5982 p hg
    simpa only [d7, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d7, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5986 p hg
    simpa only [d7, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5988 (p : Pattern) (guard : d1233 p = 1) : d0 p ≤ (0 : Int) + d39 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5984 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5989 (p : Pattern) (guard : d1233 p = 1) : d7 p ≤ (0 : Int) + d40 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d7, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5988 p hg
    simpa only [d7, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d7, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5986 p hg
    simpa only [d7, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5990 (p : Pattern) (guard : d1233 p = 1) : d7 p ≤ (0 : Int) + d41 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5987 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5991 (p : Pattern) (guard : d1233 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare5992 (p : Pattern) (guard : d1233 p = 1) : d2 p ≤ (0 : Int) + d659 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d1233, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d1233, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5993 (p : Pattern) (guard : d1233 p = 1) : d2 p ≤ (0 : Int) + d660 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5991 p hg
    simpa only [d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5992 p hg
    simpa only [d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5994 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5995 (p : Pattern) (guard : d1233 p = 1) : d2 p ≤ (0 : Int) + d262 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d1233, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5994 p hg
    simpa only [d1233, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5996 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare5997 (p : Pattern) (guard : d1233 p = 1) : d4 p ≤ (0 : Int) + d58 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5996 p hg
    simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5998 (p : Pattern) (guard : d1233 p = 1) : d54 p ≤ (0 : Int) + d661 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d54, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5995 p hg
    simpa only [d54, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d54, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5997 p hg
    simpa only [d54, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5999 (p : Pattern) (guard : d1233 p = 1) : d55 p ≤ (0 : Int) + d662 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d55, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5993 p hg
    simpa only [d55, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d55, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5998 p hg
    simpa only [d55, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6000 (p : Pattern) (guard : d1233 p = 1) : d56 p ≤ (0 : Int) + d663 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d56, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5987 p hg
    simpa only [d56, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d56, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5999 p hg
    simpa only [d56, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6001 (p : Pattern) (guard : d1233 p = 1) : d2 p ≤ (0 : Int) + d664 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5991 p hg
    simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5995 p hg
    simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6002 (p : Pattern) (guard : d1233 p = 1) : d55 p ≤ (0 : Int) + d665 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d55, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6001 p hg
    simpa only [d55, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d55, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5998 p hg
    simpa only [d55, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6003 (p : Pattern) (guard : d1233 p = 1) : d56 p ≤ (0 : Int) + d666 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d56, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d56, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d56, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d56, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6004 (p : Pattern) (guard : d1233 p = 1) : d56 p ≤ (0 : Int) + d667 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6000 p hg
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6003 p hg
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6005 (p : Pattern) (guard : d1233 p = 1) : d57 p ≤ (0 : Int) + d668 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d57, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5990 p hg
    simpa only [d57, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d57, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6004 p hg
    simpa only [d57, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6006 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6007 (p : Pattern) (guard : d1233 p = 1) : d8 p ≤ (0 : Int) + d16 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1233, d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6006 p hg
    simpa only [d1233, d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6008 (p : Pattern) (guard : d1233 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare6009 (p : Pattern) (guard : d1233 p = 1) : d10 p ≤ (0 : Int) + d37 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d10, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6007 p hg
    simpa only [d10, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d10, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6008 p hg
    simpa only [d10, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6010 (p : Pattern) (guard : d1233 p = 1) : d11 p ≤ (0 : Int) + d42 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d11, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6007 p hg
    simpa only [d11, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d11, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6009 p hg
    simpa only [d11, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6011 (p : Pattern) (guard : d1233 p = 1) : d12 p ≤ (0 : Int) + d43 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d12, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d12, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d12, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6010 p hg
    simpa only [d12, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6012 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6013 (p : Pattern) (guard : d1233 p = 1) : d9 p ≤ (0 : Int) + d262 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d9, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d1233, d9, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d9, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d1233, d9, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6014 (p : Pattern) (guard : d1233 p = 1) : d58 p ≤ (0 : Int) + d58 p := by
  omega
theorem compare6015 (p : Pattern) (guard : d1233 p = 1) : d59 p ≤ (0 : Int) + d661 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d59, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6013 p hg
    simpa only [d59, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d59, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6014 p hg
    simpa only [d59, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6016 (p : Pattern) (guard : d1233 p = 1) : d60 p ≤ (0 : Int) + d669 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d60, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6013 p hg
    simpa only [d60, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d60, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6015 p hg
    simpa only [d60, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6017 (p : Pattern) (guard : d1233 p = 1) : d61 p ≤ (0 : Int) + d670 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d61, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6010 p hg
    simpa only [d61, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d61, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6016 p hg
    simpa only [d61, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6018 (p : Pattern) (guard : d1233 p = 1) : d62 p ≤ (0 : Int) + d671 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d62, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6003 p hg
    simpa only [d62, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d62, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6017 p hg
    simpa only [d62, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6019 (p : Pattern) (guard : d1233 p = 1) : d63 p ≤ (0 : Int) + d672 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d63, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6011 p hg
    simpa only [d63, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d63, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6018 p hg
    simpa only [d63, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
