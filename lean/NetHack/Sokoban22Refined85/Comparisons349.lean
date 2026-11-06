/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons348
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48860 (p : Pattern) (guard : d8113 p = 1) : d1218 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1218, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47755 p hg
    simpa only [d8113, d1218, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1218, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47762 p hg
    simpa only [d8113, d1218, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48861 (p : Pattern) (guard : d8119 p = 1) : d1219 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1219, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48860 p hg
    simpa only [d8119, d1219, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1219, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48812 p hg
    simpa only [d8119, d1219, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48862 (p : Pattern) (guard : d8120 p = 1) : d1248 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1248, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48859 p hg
    simpa only [d8120, d1248, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1248, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48861 p hg
    simpa only [d8120, d1248, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48863 (p : Pattern) (guard : d8121 p = 1) : d1249 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1249, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48852 p hg
    simpa only [d8121, d1249, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1249, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48862 p hg
    simpa only [d8121, d1249, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48864 (p : Pattern) (guard : d8108 p = 1) : d1250 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1250, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48782 p hg
    simpa only [d8108, d1250, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1250, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48822 p hg
    simpa only [d8108, d1250, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48865 (p : Pattern) (guard : d8113 p = 1) : d1179 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1179, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48831 p hg
    simpa only [d8113, d1179, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1179, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1179, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48866 (p : Pattern) (guard : d8114 p = 1) : d1251 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1251, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48864 p hg
    simpa only [d8114, d1251, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1251, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48865 p hg
    simpa only [d8114, d1251, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48867 (p : Pattern) (guard : d8120 p = 1) : d1252 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1252, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48866 p hg
    simpa only [d8120, d1252, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1252, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48820 p hg
    simpa only [d8120, d1252, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48868 (p : Pattern) (guard : d8107 p = 1) : d1193 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34830 p hg
    simpa only [d8107, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48856 p hg
    simpa only [d8107, d1193, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48869 (p : Pattern) (guard : d8113 p = 1) : d1253 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1253, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48868 p hg
    simpa only [d8113, d1253, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1253, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8113, d1253, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48870 (p : Pattern) (guard : d8119 p = 1) : d1254 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1254, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48869 p hg
    simpa only [d8119, d1254, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1254, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48824 p hg
    simpa only [d8119, d1254, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48871 (p : Pattern) (guard : d8125 p = 1) : d1255 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1255, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48870 p hg
    simpa only [d8125, d1255, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1255, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48827 p hg
    simpa only [d8125, d1255, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48872 (p : Pattern) (guard : d8126 p = 1) : d1256 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1256, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48867 p hg
    simpa only [d8126, d1256, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1256, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48871 p hg
    simpa only [d8126, d1256, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48873 (p : Pattern) (guard : d8127 p = 1) : d1257 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1257, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48863 p hg
    simpa only [d8127, d1257, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1257, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48872 p hg
    simpa only [d8127, d1257, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48874 (p : Pattern) (guard : d8108 p = 1) : d1178 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48807 p hg
    simpa only [d8108, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48835 p hg
    simpa only [d8108, d1178, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48875 (p : Pattern) (guard : d8113 p = 1) : d1179 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48822 p hg
    simpa only [d8113, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1179, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48876 (p : Pattern) (guard : d8114 p = 1) : d1180 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48874 p hg
    simpa only [d8114, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48875 p hg
    simpa only [d8114, d1180, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48877 (p : Pattern) (guard : d8119 p = 1) : d1183 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48784 p hg
    simpa only [d8119, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1183, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48878 (p : Pattern) (guard : d8120 p = 1) : d1184 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48876 p hg
    simpa only [d8120, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48877 p hg
    simpa only [d8120, d1184, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48879 (p : Pattern) (guard : d8107 p = 1) : d1185 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34847 p hg
    simpa only [d8107, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47804 p hg
    simpa only [d8107, d1185, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48880 (p : Pattern) (guard : d8113 p = 1) : d1186 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48879 p hg
    simpa only [d8113, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47831 p hg
    simpa only [d8113, d1186, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48881 (p : Pattern) (guard : d8119 p = 1) : d1187 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48880 p hg
    simpa only [d8119, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48824 p hg
    simpa only [d8119, d1187, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48882 (p : Pattern) (guard : d8125 p = 1) : d1190 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48881 p hg
    simpa only [d8125, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48827 p hg
    simpa only [d8125, d1190, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48883 (p : Pattern) (guard : d8126 p = 1) : d1191 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48878 p hg
    simpa only [d8126, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48882 p hg
    simpa only [d8126, d1191, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48884 (p : Pattern) (guard : d8113 p = 1) : d1202 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1202, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34768 p hg
    simpa only [d8113, d1202, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1202, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1202, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48885 (p : Pattern) (guard : d8119 p = 1) : d1203 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1203, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48884 p hg
    simpa only [d8119, d1203, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1203, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38150 p hg
    simpa only [d8119, d1203, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48886 (p : Pattern) (guard : d8125 p = 1) : d1204 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1204, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48885 p hg
    simpa only [d8125, d1204, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1204, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8125, d1204, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48887 (p : Pattern) (guard : d8131 p = 1) : d1205 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1205, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48886 p hg
    simpa only [d8131, d1205, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1205, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41400 p hg
    simpa only [d8131, d1205, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48888 (p : Pattern) (guard : d8132 p = 1) : d1258 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1258, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48883 p hg
    simpa only [d8132, d1258, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1258, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48887 p hg
    simpa only [d8132, d1258, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48889 (p : Pattern) (guard : d8133 p = 1) : d1259 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1259, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48873 p hg
    simpa only [d8133, d1259, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1259, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48888 p hg
    simpa only [d8133, d1259, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48890 (p : Pattern) (guard : d8101 p = 1) : d345 p ≤ (0 : Int) + d345 p := by
  omega
theorem compare48891 (p : Pattern) (guard : d8102 p = 1) : d1152 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34753 p hg
    simpa only [d8102, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48890 p hg
    simpa only [d8102, d1152, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48892 (p : Pattern) (guard : d8108 p = 1) : d1194 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48891 p hg
    simpa only [d8108, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48868 p hg
    simpa only [d8108, d1194, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48893 (p : Pattern) (guard : d8113 p = 1) : d1179 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48835 p hg
    simpa only [d8113, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1179, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48894 (p : Pattern) (guard : d8114 p = 1) : d1195 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48892 p hg
    simpa only [d8114, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48893 p hg
    simpa only [d8114, d1195, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48895 (p : Pattern) (guard : d8107 p = 1) : d1212 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1212, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34859 p hg
    simpa only [d8107, d1212, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1212, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1212, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48896 (p : Pattern) (guard : d8112 p = 1) : d1158 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d8112, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48897 (p : Pattern) (guard : d8113 p = 1) : d1213 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1213, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48895 p hg
    simpa only [d8113, d1213, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1213, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48896 p hg
    simpa only [d8113, d1213, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48898 (p : Pattern) (guard : d8112 p = 1) : d1160 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34869 p hg
    simpa only [d8112, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48899 (p : Pattern) (guard : d8118 p = 1) : d1161 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48898 p hg
    simpa only [d8118, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34871 p hg
    simpa only [d8118, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48900 (p : Pattern) (guard : d8119 p = 1) : d1214 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1214, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48897 p hg
    simpa only [d8119, d1214, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1214, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48899 p hg
    simpa only [d8119, d1214, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48901 (p : Pattern) (guard : d8120 p = 1) : d1260 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1260, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48894 p hg
    simpa only [d8120, d1260, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1260, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48900 p hg
    simpa only [d8120, d1260, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48902 (p : Pattern) (guard : d8107 p = 1) : d1197 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34878 p hg
    simpa only [d8107, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47893 p hg
    simpa only [d8107, d1197, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48903 (p : Pattern) (guard : d8113 p = 1) : d1198 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48902 p hg
    simpa only [d8113, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47846 p hg
    simpa only [d8113, d1198, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48904 (p : Pattern) (guard : d8118 p = 1) : d1182 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47831 p hg
    simpa only [d8118, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1182, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48905 (p : Pattern) (guard : d8119 p = 1) : d1199 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48903 p hg
    simpa only [d8119, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48904 p hg
    simpa only [d8119, d1199, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48906 (p : Pattern) (guard : d8118 p = 1) : d1218 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8118, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8118, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48907 (p : Pattern) (guard : d8123 p = 1) : d1173 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8123, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d8123, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48908 (p : Pattern) (guard : d8124 p = 1) : d1219 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48906 p hg
    simpa only [d8124, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48907 p hg
    simpa only [d8124, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48909 (p : Pattern) (guard : d8125 p = 1) : d1261 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1261, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48905 p hg
    simpa only [d8125, d1261, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1261, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48908 p hg
    simpa only [d8125, d1261, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48910 (p : Pattern) (guard : d8126 p = 1) : d1262 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1262, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48901 p hg
    simpa only [d8126, d1262, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1262, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48909 p hg
    simpa only [d8126, d1262, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48911 (p : Pattern) (guard : d8112 p = 1) : d1177 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34909 p hg
    simpa only [d8112, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48912 (p : Pattern) (guard : d8113 p = 1) : d1177 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48835 p hg
    simpa only [d8113, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48911 p hg
    simpa only [d8113, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48913 (p : Pattern) (guard : d8118 p = 1) : d1179 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48911 p hg
    simpa only [d8118, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48914 (p : Pattern) (guard : d8119 p = 1) : d1263 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1263, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48912 p hg
    simpa only [d8119, d1263, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1263, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48913 p hg
    simpa only [d8119, d1263, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48915 (p : Pattern) (guard : d8124 p = 1) : d1183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48824 p hg
    simpa only [d8124, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48916 (p : Pattern) (guard : d8125 p = 1) : d1264 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1264, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48914 p hg
    simpa only [d8125, d1264, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1264, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48915 p hg
    simpa only [d8125, d1264, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48917 (p : Pattern) (guard : d8112 p = 1) : d1177 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34927 p hg
    simpa only [d8112, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1177, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48918 (p : Pattern) (guard : d8118 p = 1) : d1225 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1225, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48917 p hg
    simpa only [d8118, d1225, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1225, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8118, d1225, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48919 (p : Pattern) (guard : d8123 p = 1) : d1182 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8123, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48920 (p : Pattern) (guard : d8124 p = 1) : d1226 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1226, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48918 p hg
    simpa only [d8124, d1226, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1226, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48919 p hg
    simpa only [d8124, d1226, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48921 (p : Pattern) (guard : d8123 p = 1) : d1188 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8123, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48922 (p : Pattern) (guard : d8129 p = 1) : d1189 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48921 p hg
    simpa only [d8129, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48923 (p : Pattern) (guard : d8130 p = 1) : d1227 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1227, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48920 p hg
    simpa only [d8130, d1227, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1227, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48922 p hg
    simpa only [d8130, d1227, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48924 (p : Pattern) (guard : d8131 p = 1) : d1265 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1265, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48916 p hg
    simpa only [d8131, d1265, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1265, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48923 p hg
    simpa only [d8131, d1265, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48925 (p : Pattern) (guard : d8132 p = 1) : d1266 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1266, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48910 p hg
    simpa only [d8132, d1266, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1266, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48924 p hg
    simpa only [d8132, d1266, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48926 (p : Pattern) (guard : d8113 p = 1) : d1222 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48868 p hg
    simpa only [d8113, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48911 p hg
    simpa only [d8113, d1222, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48927 (p : Pattern) (guard : d8119 p = 1) : d1223 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48926 p hg
    simpa only [d8119, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48913 p hg
    simpa only [d8119, d1223, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48928 (p : Pattern) (guard : d8125 p = 1) : d1224 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48927 p hg
    simpa only [d8125, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48915 p hg
    simpa only [d8125, d1224, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48929 (p : Pattern) (guard : d8112 p = 1) : d1177 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35073 p hg
    simpa only [d8112, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1177, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48930 (p : Pattern) (guard : d8118 p = 1) : d1225 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48929 p hg
    simpa only [d8118, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8118, d1225, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48931 (p : Pattern) (guard : d8124 p = 1) : d1226 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48930 p hg
    simpa only [d8124, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48919 p hg
    simpa only [d8124, d1226, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48932 (p : Pattern) (guard : d8130 p = 1) : d1227 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48931 p hg
    simpa only [d8130, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48922 p hg
    simpa only [d8130, d1227, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48933 (p : Pattern) (guard : d8131 p = 1) : d1228 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48928 p hg
    simpa only [d8131, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48932 p hg
    simpa only [d8131, d1228, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48934 (p : Pattern) (guard : d8137 p = 1) : d1267 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1267, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48933 p hg
    simpa only [d8137, d1267, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1267, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1267, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48935 (p : Pattern) (guard : d8138 p = 1) : d1268 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1268, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48925 p hg
    simpa only [d8138, d1268, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1268, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48934 p hg
    simpa only [d8138, d1268, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48936 (p : Pattern) (guard : d8139 p = 1) : d1269 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1269, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48889 p hg
    simpa only [d8139, d1269, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1269, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48935 p hg
    simpa only [d8139, d1269, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48937 (p : Pattern) (guard : d8140 p = 1) : d1270 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d1270, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48842 p hg
    simpa only [d8140, d1270, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d1270, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48936 p hg
    simpa only [d8140, d1270, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48938 (p : Pattern) (guard : d8096 p = 1) : d337 p ≤ (0 : Int) + d337 p := by
  omega
theorem compare48939 (p : Pattern) (guard : d8097 p = 1) : d1151 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d8097, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48938 p hg
    simpa only [d8097, d1151, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48940 (p : Pattern) (guard : d8103 p = 1) : d1153 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48939 p hg
    simpa only [d8103, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48891 p hg
    simpa only [d8103, d1153, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48941 (p : Pattern) (guard : d8108 p = 1) : d1155 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48807 p hg
    simpa only [d8108, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34952 p hg
    simpa only [d8108, d1155, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48942 (p : Pattern) (guard : d8109 p = 1) : d1156 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48940 p hg
    simpa only [d8109, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48941 p hg
    simpa only [d8109, d1156, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48943 (p : Pattern) (guard : d8102 p = 1) : d1157 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34955 p hg
    simpa only [d8102, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47689 p hg
    simpa only [d8102, d1157, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48944 (p : Pattern) (guard : d8107 p = 1) : d1158 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34957 p hg
    simpa only [d8107, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1158, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48945 (p : Pattern) (guard : d8108 p = 1) : d1159 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48943 p hg
    simpa only [d8108, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48944 p hg
    simpa only [d8108, d1159, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48946 (p : Pattern) (guard : d8107 p = 1) : d1160 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34960 p hg
    simpa only [d8107, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1160, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48947 (p : Pattern) (guard : d8113 p = 1) : d1161 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48946 p hg
    simpa only [d8113, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34649 p hg
    simpa only [d8113, d1161, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48948 (p : Pattern) (guard : d8114 p = 1) : d1162 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48945 p hg
    simpa only [d8114, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48947 p hg
    simpa only [d8114, d1162, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48949 (p : Pattern) (guard : d8115 p = 1) : d1163 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48942 p hg
    simpa only [d8115, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48948 p hg
    simpa only [d8115, d1163, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48950 (p : Pattern) (guard : d8101 p = 1) : d352 p ≤ (0 : Int) + d352 p := by
  omega
theorem compare48951 (p : Pattern) (guard : d8102 p = 1) : d1164 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d8102, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48950 p hg
    simpa only [d8102, d1164, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48952 (p : Pattern) (guard : d8108 p = 1) : d1166 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48951 p hg
    simpa only [d8108, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47894 p hg
    simpa only [d8108, d1166, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48953 (p : Pattern) (guard : d8113 p = 1) : d1168 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47805 p hg
    simpa only [d8113, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34996 p hg
    simpa only [d8113, d1168, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48954 (p : Pattern) (guard : d8114 p = 1) : d1169 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48952 p hg
    simpa only [d8114, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48953 p hg
    simpa only [d8114, d1169, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48955 (p : Pattern) (guard : d8113 p = 1) : d1172 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48857 p hg
    simpa only [d8113, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47762 p hg
    simpa only [d8113, d1172, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48956 (p : Pattern) (guard : d8119 p = 1) : d1174 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48955 p hg
    simpa only [d8119, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48812 p hg
    simpa only [d8119, d1174, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48957 (p : Pattern) (guard : d8120 p = 1) : d1175 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48954 p hg
    simpa only [d8120, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48956 p hg
    simpa only [d8120, d1175, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48958 (p : Pattern) (guard : d8121 p = 1) : d1176 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48949 p hg
    simpa only [d8121, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48957 p hg
    simpa only [d8121, d1176, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48959 (p : Pattern) (guard : d8127 p = 1) : d1192 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48958 p hg
    simpa only [d8127, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48883 p hg
    simpa only [d8127, d1192, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48960 (p : Pattern) (guard : d8119 p = 1) : d1183 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48809 p hg
    simpa only [d8119, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1183, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48961 (p : Pattern) (guard : d8120 p = 1) : d1196 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48894 p hg
    simpa only [d8120, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48960 p hg
    simpa only [d8120, d1196, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48962 (p : Pattern) (guard : d8125 p = 1) : d1200 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48905 p hg
    simpa only [d8125, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48827 p hg
    simpa only [d8125, d1200, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48963 (p : Pattern) (guard : d8126 p = 1) : d1201 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48961 p hg
    simpa only [d8126, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48962 p hg
    simpa only [d8126, d1201, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48964 (p : Pattern) (guard : d8113 p = 1) : d1202 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34952 p hg
    simpa only [d8113, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1202, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48965 (p : Pattern) (guard : d8119 p = 1) : d1203 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48964 p hg
    simpa only [d8119, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38150 p hg
    simpa only [d8119, d1203, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48966 (p : Pattern) (guard : d8125 p = 1) : d1204 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48965 p hg
    simpa only [d8125, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8125, d1204, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48967 (p : Pattern) (guard : d8131 p = 1) : d1205 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48966 p hg
    simpa only [d8131, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41412 p hg
    simpa only [d8131, d1205, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48968 (p : Pattern) (guard : d8132 p = 1) : d1206 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48963 p hg
    simpa only [d8132, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48967 p hg
    simpa only [d8132, d1206, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48969 (p : Pattern) (guard : d8133 p = 1) : d1207 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48959 p hg
    simpa only [d8133, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48968 p hg
    simpa only [d8133, d1207, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48970 (p : Pattern) (guard : d8108 p = 1) : d1209 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48854 p hg
    simpa only [d8108, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48879 p hg
    simpa only [d8108, d1209, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48971 (p : Pattern) (guard : d8113 p = 1) : d1210 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48868 p hg
    simpa only [d8113, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1210, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48972 (p : Pattern) (guard : d8114 p = 1) : d1211 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48970 p hg
    simpa only [d8114, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48971 p hg
    simpa only [d8114, d1211, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48973 (p : Pattern) (guard : d8107 p = 1) : d1212 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35034 p hg
    simpa only [d8107, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1212, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48974 (p : Pattern) (guard : d8113 p = 1) : d1213 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48973 p hg
    simpa only [d8113, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48896 p hg
    simpa only [d8113, d1213, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48975 (p : Pattern) (guard : d8119 p = 1) : d1214 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48974 p hg
    simpa only [d8119, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48899 p hg
    simpa only [d8119, d1214, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48976 (p : Pattern) (guard : d8120 p = 1) : d1215 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48972 p hg
    simpa only [d8120, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48975 p hg
    simpa only [d8120, d1215, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48977 (p : Pattern) (guard : d8106 p = 1) : d354 p ≤ (0 : Int) + d354 p := by
  omega
theorem compare48978 (p : Pattern) (guard : d8107 p = 1) : d1154 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35042 p hg
    simpa only [d8107, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48977 p hg
    simpa only [d8107, d1154, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48979 (p : Pattern) (guard : d8113 p = 1) : d1216 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48978 p hg
    simpa only [d8113, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47926 p hg
    simpa only [d8113, d1216, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48980 (p : Pattern) (guard : d8118 p = 1) : d1182 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47846 p hg
    simpa only [d8118, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1182, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48981 (p : Pattern) (guard : d8119 p = 1) : d1217 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48979 p hg
    simpa only [d8119, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48980 p hg
    simpa only [d8119, d1217, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48982 (p : Pattern) (guard : d8118 p = 1) : d1218 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47831 p hg
    simpa only [d8118, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8118, d1218, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48983 (p : Pattern) (guard : d8124 p = 1) : d1219 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48982 p hg
    simpa only [d8124, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48907 p hg
    simpa only [d8124, d1219, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48984 (p : Pattern) (guard : d8125 p = 1) : d1220 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48981 p hg
    simpa only [d8125, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48983 p hg
    simpa only [d8125, d1220, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48985 (p : Pattern) (guard : d8126 p = 1) : d1221 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48976 p hg
    simpa only [d8126, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48984 p hg
    simpa only [d8126, d1221, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48986 (p : Pattern) (guard : d8132 p = 1) : d1229 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48985 p hg
    simpa only [d8132, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48933 p hg
    simpa only [d8132, d1229, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48987 (p : Pattern) (guard : d8113 p = 1) : d1230 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48879 p hg
    simpa only [d8113, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48917 p hg
    simpa only [d8113, d1230, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48988 (p : Pattern) (guard : d8119 p = 1) : d1231 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48987 p hg
    simpa only [d8119, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48913 p hg
    simpa only [d8119, d1231, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48989 (p : Pattern) (guard : d8125 p = 1) : d1232 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48988 p hg
    simpa only [d8125, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48915 p hg
    simpa only [d8125, d1232, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48990 (p : Pattern) (guard : d8112 p = 1) : d1177 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35454 p hg
    simpa only [d8112, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1177, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48991 (p : Pattern) (guard : d8118 p = 1) : d1225 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48990 p hg
    simpa only [d8118, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8118, d1225, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48992 (p : Pattern) (guard : d8124 p = 1) : d1226 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48991 p hg
    simpa only [d8124, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48919 p hg
    simpa only [d8124, d1226, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48993 (p : Pattern) (guard : d8130 p = 1) : d1227 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48992 p hg
    simpa only [d8130, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48922 p hg
    simpa only [d8130, d1227, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48994 (p : Pattern) (guard : d8131 p = 1) : d1233 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48989 p hg
    simpa only [d8131, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48993 p hg
    simpa only [d8131, d1233, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48995 (p : Pattern) (guard : d8137 p = 1) : d1234 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48994 p hg
    simpa only [d8137, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1234, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48996 (p : Pattern) (guard : d8138 p = 1) : d1235 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48986 p hg
    simpa only [d8138, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48995 p hg
    simpa only [d8138, d1235, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48997 (p : Pattern) (guard : d8139 p = 1) : d1236 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48969 p hg
    simpa only [d8139, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48996 p hg
    simpa only [d8139, d1236, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48998 (p : Pattern) (guard : d8101 p = 1) : d344 p ≤ (0 : Int) + d344 p := by
  omega
theorem compare48999 (p : Pattern) (guard : d8102 p = 1) : d1271 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1271, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35105 p hg
    simpa only [d8102, d1271, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1271, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48998 p hg
    simpa only [d8102, d1271, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
