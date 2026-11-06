/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons354
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49700 (p : Pattern) (guard : d8123 p = 1) : d968 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41479 p hg
    simpa only [d8123, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49701 (p : Pattern) (guard : d8129 p = 1) : d1099 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1099, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49700 p hg
    simpa only [d8129, d1099, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1099, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d8129, d1099, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49702 (p : Pattern) (guard : d8135 p = 1) : d1102 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1102, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49701 p hg
    simpa only [d8135, d1102, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1102, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48129 p hg
    simpa only [d8135, d1102, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49703 (p : Pattern) (guard : d8136 p = 1) : d1103 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1103, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49699 p hg
    simpa only [d8136, d1103, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1103, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49702 p hg
    simpa only [d8136, d1103, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49704 (p : Pattern) (guard : d8142 p = 1) : d1105 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1105, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49703 p hg
    simpa only [d8142, d1105, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1105, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1105, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49705 (p : Pattern) (guard : d8143 p = 1) : d1106 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1106, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49696 p hg
    simpa only [d8143, d1106, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1106, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49704 p hg
    simpa only [d8143, d1106, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49706 (p : Pattern) (guard : d8144 p = 1) : d1107 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1107, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49671 p hg
    simpa only [d8144, d1107, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1107, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49705 p hg
    simpa only [d8144, d1107, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49707 (p : Pattern) (guard : d8145 p = 1) : d1108 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d1108, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49564 p hg
    simpa only [d8145, d1108, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d1108, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49706 p hg
    simpa only [d8145, d1108, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49708 (p : Pattern) (guard : d8107 p = 1) : d346 p ≤ (0 : Int) + d346 p := by
  omega
theorem compare49709 (p : Pattern) (guard : d8108 p = 1) : d949 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35567 p hg
    simpa only [d8108, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49708 p hg
    simpa only [d8108, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49710 (p : Pattern) (guard : d8113 p = 1) : d951 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48144 p hg
    simpa only [d8113, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49547 p hg
    simpa only [d8113, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49711 (p : Pattern) (guard : d8114 p = 1) : d952 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49709 p hg
    simpa only [d8114, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49710 p hg
    simpa only [d8114, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49712 (p : Pattern) (guard : d8113 p = 1) : d953 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48147 p hg
    simpa only [d8113, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49480 p hg
    simpa only [d8113, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49713 (p : Pattern) (guard : d8118 p = 1) : d954 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35579 p hg
    simpa only [d8118, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49714 (p : Pattern) (guard : d8119 p = 1) : d955 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49712 p hg
    simpa only [d8119, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49713 p hg
    simpa only [d8119, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49715 (p : Pattern) (guard : d8120 p = 1) : d956 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49711 p hg
    simpa only [d8120, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49714 p hg
    simpa only [d8120, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49716 (p : Pattern) (guard : d8112 p = 1) : d369 p ≤ (0 : Int) + d369 p := by
  omega
theorem compare49717 (p : Pattern) (guard : d8113 p = 1) : d957 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35593 p hg
    simpa only [d8113, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49716 p hg
    simpa only [d8113, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49718 (p : Pattern) (guard : d8118 p = 1) : d958 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48155 p hg
    simpa only [d8118, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49593 p hg
    simpa only [d8118, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49719 (p : Pattern) (guard : d8119 p = 1) : d959 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49717 p hg
    simpa only [d8119, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49718 p hg
    simpa only [d8119, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49720 (p : Pattern) (guard : d8124 p = 1) : d962 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49643 p hg
    simpa only [d8124, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49485 p hg
    simpa only [d8124, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49721 (p : Pattern) (guard : d8125 p = 1) : d963 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49719 p hg
    simpa only [d8125, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49720 p hg
    simpa only [d8125, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49722 (p : Pattern) (guard : d8126 p = 1) : d964 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49715 p hg
    simpa only [d8126, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49721 p hg
    simpa only [d8126, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49723 (p : Pattern) (guard : d8132 p = 1) : d977 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49722 p hg
    simpa only [d8132, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49665 p hg
    simpa only [d8132, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49724 (p : Pattern) (guard : d8119 p = 1) : d979 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49672 p hg
    simpa only [d8119, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49558 p hg
    simpa only [d8119, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49725 (p : Pattern) (guard : d8118 p = 1) : d968 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48165 p hg
    simpa only [d8118, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49726 (p : Pattern) (guard : d8124 p = 1) : d969 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49725 p hg
    simpa only [d8124, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49727 (p : Pattern) (guard : d8125 p = 1) : d980 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49724 p hg
    simpa only [d8125, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49726 p hg
    simpa only [d8125, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49728 (p : Pattern) (guard : d8123 p = 1) : d972 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48169 p hg
    simpa only [d8123, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49729 (p : Pattern) (guard : d8124 p = 1) : d982 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49679 p hg
    simpa only [d8124, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49728 p hg
    simpa only [d8124, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49730 (p : Pattern) (guard : d8130 p = 1) : d983 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49729 p hg
    simpa only [d8130, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49731 (p : Pattern) (guard : d8131 p = 1) : d984 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49727 p hg
    simpa only [d8131, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49730 p hg
    simpa only [d8131, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49732 (p : Pattern) (guard : d8118 p = 1) : d985 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38268 p hg
    simpa only [d8118, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49733 (p : Pattern) (guard : d8124 p = 1) : d986 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49732 p hg
    simpa only [d8124, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d8124, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49734 (p : Pattern) (guard : d8130 p = 1) : d987 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49733 p hg
    simpa only [d8130, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8130, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49735 (p : Pattern) (guard : d8136 p = 1) : d988 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49734 p hg
    simpa only [d8136, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41492 p hg
    simpa only [d8136, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49736 (p : Pattern) (guard : d8137 p = 1) : d989 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49731 p hg
    simpa only [d8137, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49735 p hg
    simpa only [d8137, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49737 (p : Pattern) (guard : d8138 p = 1) : d990 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49723 p hg
    simpa only [d8138, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49736 p hg
    simpa only [d8138, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49738 (p : Pattern) (guard : d8113 p = 1) : d991 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35639 p hg
    simpa only [d8113, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49573 p hg
    simpa only [d8113, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49739 (p : Pattern) (guard : d8118 p = 1) : d992 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d8118, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49740 (p : Pattern) (guard : d8119 p = 1) : d993 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49738 p hg
    simpa only [d8119, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49739 p hg
    simpa only [d8119, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49741 (p : Pattern) (guard : d8118 p = 1) : d994 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d8118, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49742 (p : Pattern) (guard : d8124 p = 1) : d995 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49741 p hg
    simpa only [d8124, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49676 p hg
    simpa only [d8124, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49743 (p : Pattern) (guard : d8125 p = 1) : d996 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49740 p hg
    simpa only [d8125, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49742 p hg
    simpa only [d8125, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49744 (p : Pattern) (guard : d8117 p = 1) : d361 p ≤ (0 : Int) + d361 p := by
  omega
theorem compare49745 (p : Pattern) (guard : d8118 p = 1) : d997 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35660 p hg
    simpa only [d8118, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49744 p hg
    simpa only [d8118, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49746 (p : Pattern) (guard : d8123 p = 1) : d960 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48186 p hg
    simpa only [d8123, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49747 (p : Pattern) (guard : d8124 p = 1) : d998 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49745 p hg
    simpa only [d8124, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49746 p hg
    simpa only [d8124, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49748 (p : Pattern) (guard : d8129 p = 1) : d962 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49680 p hg
    simpa only [d8129, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8681 p hg
    simpa only [d8129, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49749 (p : Pattern) (guard : d8130 p = 1) : d999 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49747 p hg
    simpa only [d8130, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49748 p hg
    simpa only [d8130, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49750 (p : Pattern) (guard : d8131 p = 1) : d1000 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49743 p hg
    simpa only [d8131, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49749 p hg
    simpa only [d8131, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49751 (p : Pattern) (guard : d8123 p = 1) : d966 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35687 p hg
    simpa only [d8123, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49752 (p : Pattern) (guard : d8129 p = 1) : d1004 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49751 p hg
    simpa only [d8129, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d8129, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49753 (p : Pattern) (guard : d8135 p = 1) : d1005 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49752 p hg
    simpa only [d8135, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48195 p hg
    simpa only [d8135, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49754 (p : Pattern) (guard : d8136 p = 1) : d1006 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49699 p hg
    simpa only [d8136, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49753 p hg
    simpa only [d8136, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49755 (p : Pattern) (guard : d8137 p = 1) : d1007 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49750 p hg
    simpa only [d8137, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49754 p hg
    simpa only [d8137, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49756 (p : Pattern) (guard : d8118 p = 1) : d1008 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38277 p hg
    simpa only [d8118, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49593 p hg
    simpa only [d8118, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49757 (p : Pattern) (guard : d8124 p = 1) : d1009 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49756 p hg
    simpa only [d8124, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49687 p hg
    simpa only [d8124, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49758 (p : Pattern) (guard : d8130 p = 1) : d1010 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49757 p hg
    simpa only [d8130, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49690 p hg
    simpa only [d8130, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49759 (p : Pattern) (guard : d8123 p = 1) : d966 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41498 p hg
    simpa only [d8123, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49760 (p : Pattern) (guard : d8129 p = 1) : d1004 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49759 p hg
    simpa only [d8129, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d8129, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49761 (p : Pattern) (guard : d8135 p = 1) : d1005 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49760 p hg
    simpa only [d8135, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48195 p hg
    simpa only [d8135, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49762 (p : Pattern) (guard : d8136 p = 1) : d1011 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49758 p hg
    simpa only [d8136, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49761 p hg
    simpa only [d8136, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49763 (p : Pattern) (guard : d8142 p = 1) : d1012 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49762 p hg
    simpa only [d8142, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49764 (p : Pattern) (guard : d8143 p = 1) : d1013 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49755 p hg
    simpa only [d8143, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49763 p hg
    simpa only [d8143, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49765 (p : Pattern) (guard : d8144 p = 1) : d1014 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49737 p hg
    simpa only [d8144, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49764 p hg
    simpa only [d8144, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49766 (p : Pattern) (guard : d8112 p = 1) : d355 p ≤ (0 : Int) + d355 p := by
  omega
theorem compare49767 (p : Pattern) (guard : d8113 p = 1) : d1042 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1042, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35707 p hg
    simpa only [d8113, d1042, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1042, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49766 p hg
    simpa only [d8113, d1042, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49768 (p : Pattern) (guard : d8118 p = 1) : d1044 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1044, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48209 p hg
    simpa only [d8118, d1044, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1044, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49608 p hg
    simpa only [d8118, d1044, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49769 (p : Pattern) (guard : d8119 p = 1) : d1045 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1045, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49767 p hg
    simpa only [d8119, d1045, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1045, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49768 p hg
    simpa only [d8119, d1045, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49770 (p : Pattern) (guard : d8118 p = 1) : d1046 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1046, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48213 p hg
    simpa only [d8118, d1046, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1046, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49593 p hg
    simpa only [d8118, d1046, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49771 (p : Pattern) (guard : d8124 p = 1) : d1048 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1048, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49770 p hg
    simpa only [d8124, d1048, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1048, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49605 p hg
    simpa only [d8124, d1048, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49772 (p : Pattern) (guard : d8125 p = 1) : d1049 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1049, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49769 p hg
    simpa only [d8125, d1049, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1049, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49771 p hg
    simpa only [d8125, d1049, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49773 (p : Pattern) (guard : d8118 p = 1) : d1109 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1109, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35757 p hg
    simpa only [d8118, d1109, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1109, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35806 p hg
    simpa only [d8118, d1109, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49774 (p : Pattern) (guard : d8124 p = 1) : d1110 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1110, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49773 p hg
    simpa only [d8124, d1110, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1110, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48232 p hg
    simpa only [d8124, d1110, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49775 (p : Pattern) (guard : d8123 p = 1) : d1051 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1051, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48234 p hg
    simpa only [d8123, d1051, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1051, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1051, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49776 (p : Pattern) (guard : d8129 p = 1) : d1055 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1055, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49775 p hg
    simpa only [d8129, d1055, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1055, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8786 p hg
    simpa only [d8129, d1055, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49777 (p : Pattern) (guard : d8130 p = 1) : d1111 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1111, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49774 p hg
    simpa only [d8130, d1111, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1111, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49776 p hg
    simpa only [d8130, d1111, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49778 (p : Pattern) (guard : d8131 p = 1) : d1112 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1112, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49772 p hg
    simpa only [d8131, d1112, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1112, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49777 p hg
    simpa only [d8131, d1112, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49779 (p : Pattern) (guard : d8118 p = 1) : d1058 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1058, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35784 p hg
    simpa only [d8118, d1058, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1058, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49608 p hg
    simpa only [d8118, d1058, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49780 (p : Pattern) (guard : d8124 p = 1) : d1060 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1060, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49779 p hg
    simpa only [d8124, d1060, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1060, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49619 p hg
    simpa only [d8124, d1060, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49781 (p : Pattern) (guard : d8130 p = 1) : d1063 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1063, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49780 p hg
    simpa only [d8130, d1063, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1063, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48039 p hg
    simpa only [d8130, d1063, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49782 (p : Pattern) (guard : d8123 p = 1) : d1059 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1059, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35798 p hg
    simpa only [d8123, d1059, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1059, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1059, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49783 (p : Pattern) (guard : d8129 p = 1) : d1065 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1065, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49782 p hg
    simpa only [d8129, d1065, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1065, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d8129, d1065, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49784 (p : Pattern) (guard : d8135 p = 1) : d1067 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1067, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49783 p hg
    simpa only [d8135, d1067, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1067, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d8135, d1067, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49785 (p : Pattern) (guard : d8136 p = 1) : d1068 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1068, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49781 p hg
    simpa only [d8136, d1068, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1068, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49784 p hg
    simpa only [d8136, d1068, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49786 (p : Pattern) (guard : d8137 p = 1) : d1113 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1113, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49778 p hg
    simpa only [d8137, d1113, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1113, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49785 p hg
    simpa only [d8137, d1113, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49787 (p : Pattern) (guard : d8118 p = 1) : d1070 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1070, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38295 p hg
    simpa only [d8118, d1070, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1070, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49744 p hg
    simpa only [d8118, d1070, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49788 (p : Pattern) (guard : d8124 p = 1) : d1071 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1071, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49787 p hg
    simpa only [d8124, d1071, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1071, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49627 p hg
    simpa only [d8124, d1071, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49789 (p : Pattern) (guard : d8130 p = 1) : d1072 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1072, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49788 p hg
    simpa only [d8130, d1072, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1072, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48251 p hg
    simpa only [d8130, d1072, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49790 (p : Pattern) (guard : d8123 p = 1) : d1059 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1059, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41506 p hg
    simpa only [d8123, d1059, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1059, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35807 p hg
    simpa only [d8123, d1059, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49791 (p : Pattern) (guard : d8129 p = 1) : d1065 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1065, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49790 p hg
    simpa only [d8129, d1065, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1065, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d8129, d1065, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49792 (p : Pattern) (guard : d8135 p = 1) : d1067 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1067, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49791 p hg
    simpa only [d8135, d1067, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1067, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d8135, d1067, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49793 (p : Pattern) (guard : d8136 p = 1) : d1114 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1114, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49789 p hg
    simpa only [d8136, d1114, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1114, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49792 p hg
    simpa only [d8136, d1114, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49794 (p : Pattern) (guard : d8142 p = 1) : d1115 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1115, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49793 p hg
    simpa only [d8142, d1115, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1115, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38307 p hg
    simpa only [d8142, d1115, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49795 (p : Pattern) (guard : d8143 p = 1) : d1116 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1116, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49786 p hg
    simpa only [d8143, d1116, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1116, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49794 p hg
    simpa only [d8143, d1116, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49796 (p : Pattern) (guard : d8118 p = 1) : d1117 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1117, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35821 p hg
    simpa only [d8118, d1117, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1117, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35855 p hg
    simpa only [d8118, d1117, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49797 (p : Pattern) (guard : d8123 p = 1) : d1118 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35846 p hg
    simpa only [d8123, d1118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49798 (p : Pattern) (guard : d8124 p = 1) : d1119 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1119, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49796 p hg
    simpa only [d8124, d1119, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1119, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49797 p hg
    simpa only [d8124, d1119, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49799 (p : Pattern) (guard : d8123 p = 1) : d1120 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1120, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48261 p hg
    simpa only [d8123, d1120, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1120, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1120, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49800 (p : Pattern) (guard : d8129 p = 1) : d1122 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1122, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49799 p hg
    simpa only [d8129, d1122, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1122, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8874 p hg
    simpa only [d8129, d1122, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49801 (p : Pattern) (guard : d8130 p = 1) : d1123 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1123, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49798 p hg
    simpa only [d8130, d1123, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1123, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49800 p hg
    simpa only [d8130, d1123, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49802 (p : Pattern) (guard : d8123 p = 1) : d1059 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1059, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35839 p hg
    simpa only [d8123, d1059, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1059, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38313 p hg
    simpa only [d8123, d1059, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49803 (p : Pattern) (guard : d8129 p = 1) : d1125 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1125, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49802 p hg
    simpa only [d8129, d1125, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1125, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48266 p hg
    simpa only [d8129, d1125, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49804 (p : Pattern) (guard : d0 p = 1) : d1130 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49805 (p : Pattern) (guard : d8135 p = 1) : d1131 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1131, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49803 p hg
    simpa only [d8135, d1131, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1131, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49804 p hg
    simpa only [d8135, d1131, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49806 (p : Pattern) (guard : d8136 p = 1) : d1132 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1132, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49801 p hg
    simpa only [d8136, d1132, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1132, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49805 p hg
    simpa only [d8136, d1132, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49807 (p : Pattern) (guard : d8123 p = 1) : d1089 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1089, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41521 p hg
    simpa only [d8123, d1089, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1089, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1089, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49808 (p : Pattern) (guard : d8129 p = 1) : d1135 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1135, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49807 p hg
    simpa only [d8129, d1135, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1135, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8887 p hg
    simpa only [d8129, d1135, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49809 (p : Pattern) (guard : d8135 p = 1) : d1136 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1136, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49808 p hg
    simpa only [d8135, d1136, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1136, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48273 p hg
    simpa only [d8135, d1136, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49810 (p : Pattern) (guard : d0 p = 1) : d1142 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49811 (p : Pattern) (guard : d8141 p = 1) : d1143 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1143, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49809 p hg
    simpa only [d8141, d1143, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1143, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49810 p hg
    simpa only [d8141, d1143, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49812 (p : Pattern) (guard : d8142 p = 1) : d1144 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1144, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49806 p hg
    simpa only [d8142, d1144, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1144, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49811 p hg
    simpa only [d8142, d1144, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49813 (p : Pattern) (guard : d8123 p = 1) : d1089 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1089, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41528 p hg
    simpa only [d8123, d1089, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1089, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1089, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49814 (p : Pattern) (guard : d8129 p = 1) : d1135 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1135, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49813 p hg
    simpa only [d8129, d1135, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1135, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8887 p hg
    simpa only [d8129, d1135, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49815 (p : Pattern) (guard : d8135 p = 1) : d1136 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1136, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49814 p hg
    simpa only [d8135, d1136, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1136, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48273 p hg
    simpa only [d8135, d1136, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49816 (p : Pattern) (guard : d0 p = 1) : d1142 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49817 (p : Pattern) (guard : d8141 p = 1) : d1143 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1143, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49815 p hg
    simpa only [d8141, d1143, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1143, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49816 p hg
    simpa only [d8141, d1143, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49818 (p : Pattern) (guard : d8147 p = 1) : d1145 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d1145, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49817 p hg
    simpa only [d8147, d1145, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d1145, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d1145, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49819 (p : Pattern) (guard : d8148 p = 1) : d1146 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d1146, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49812 p hg
    simpa only [d8148, d1146, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d1146, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49818 p hg
    simpa only [d8148, d1146, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49820 (p : Pattern) (guard : d8149 p = 1) : d1147 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d1147, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49795 p hg
    simpa only [d8149, d1147, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d1147, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49819 p hg
    simpa only [d8149, d1147, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49821 (p : Pattern) (guard : d8150 p = 1) : d1148 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d1148, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49765 p hg
    simpa only [d8150, d1148, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d1148, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49820 p hg
    simpa only [d8150, d1148, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49822 (p : Pattern) (guard : d8151 p = 1) : d1149 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49707 p hg
    simpa only [d8151, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49821 p hg
    simpa only [d8151, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49823 (p : Pattern) (guard : d8152 p = 1) : d1150 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d8152, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49822 p hg
    simpa only [d8152, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
