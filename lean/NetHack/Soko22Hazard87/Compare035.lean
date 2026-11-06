import NetHack.Soko22Hazard87.Compare034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8750 (p : Pattern) (guard : d1122 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8749 p hg
    simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8751 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1123, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8750 p hg
    simpa only [d1123, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8752 (p : Pattern) (guard : d1124 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8751 p hg
    simpa only [d1124, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1124, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8753 (p : Pattern) (guard : d1125 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8741 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8752 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8754 (p : Pattern) (guard : d1126 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1114 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8742 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8753 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8755 (p : Pattern) (guard : d1127 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8752 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8756 (p : Pattern) (guard : d1128 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8753 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1127 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8755 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8757 (p : Pattern) (guard : d1129 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8754 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1128 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8756 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8758 (p : Pattern) (guard : d1130 p = 1) : d47686 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1130, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d1130, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1129 p = 1 := by simpa only [d1130, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d1130, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8759 (p : Pattern) (guard : d1131 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1131, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d1131, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1130 p = 1 := by simpa only [d1131, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8758 p hg
    simpa only [d1131, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8760 (p : Pattern) (guard : d1132 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8744 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8761 (p : Pattern) (guard : d1133 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8760 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8762 (p : Pattern) (guard : d1134 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8761 p hg
    simpa only [d1134, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1134, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8763 (p : Pattern) (guard : d1135 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8762 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7952 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8764 (p : Pattern) (guard : d1136 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8763 p hg
    simpa only [d1136, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1136, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8765 (p : Pattern) (guard : d1137 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1136 p = 1 := by simpa only [d1137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8764 p hg
    simpa only [d1137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8766 (p : Pattern) (guard : d1138 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1138, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1138, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1137 p = 1 := by simpa only [d1138, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8765 p hg
    simpa only [d1138, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8767 (p : Pattern) (guard : d1139 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1138 p = 1 := by simpa only [d1139, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8766 p hg
    simpa only [d1139, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1139, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1139, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8768 (p : Pattern) (guard : d1140 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1139 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8767 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8769 (p : Pattern) (guard : d1141 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8755 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1140 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8770 (p : Pattern) (guard : d1142 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1128 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8756 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1141 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8769 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8771 (p : Pattern) (guard : d1143 p = 1) : d47686 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1143, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d1143, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1142 p = 1 := by simpa only [d1143, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8770 p hg
    simpa only [d1143, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8772 (p : Pattern) (guard : d1144 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1144, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d1144, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1143 p = 1 := by simpa only [d1144, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8771 p hg
    simpa only [d1144, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8773 (p : Pattern) (guard : d1145 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1131 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8759 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1144 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8772 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8774 (p : Pattern) (guard : d1146 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1144 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8772 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8775 (p : Pattern) (guard : d1147 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1145 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8773 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1146 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8774 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8776 (p : Pattern) (guard : d1148 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1147 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8775 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8777 (p : Pattern) (guard : d1149 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d1149, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8776 p hg
    simpa only [d1149, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1149, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d1149, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8778 (p : Pattern) (guard : d1150 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d1150, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1149 p = 1 := by simpa only [d1150, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8777 p hg
    simpa only [d1150, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8779 (p : Pattern) (guard : d1151 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1146 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8774 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8780 (p : Pattern) (guard : d1152 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8779 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8781 (p : Pattern) (guard : d1153 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1152 p = 1 := by simpa only [d1153, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8780 p hg
    simpa only [d1153, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1153, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d1153, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8782 (p : Pattern) (guard : d1154 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1154, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d1154, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1153 p = 1 := by simpa only [d1154, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8781 p hg
    simpa only [d1154, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8783 (p : Pattern) (guard : d1155 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8778 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1154 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8782 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8784 (p : Pattern) (guard : d1156 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1155 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8783 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8785 (p : Pattern) (guard : d1157 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1156 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8784 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8786 (p : Pattern) (guard : d1158 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1157 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8785 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8787 (p : Pattern) (guard : d1159 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1154 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8782 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8788 (p : Pattern) (guard : d1160 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1159 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8787 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8789 (p : Pattern) (guard : d1161 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1160 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8788 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8790 (p : Pattern) (guard : d1162 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1161 p = 1 := by simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8789 p hg
    simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8791 (p : Pattern) (guard : d1163 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8786 p hg
    simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1162 p = 1 := by simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8790 p hg
    simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8792 (p : Pattern) (guard : d1164 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1163 p = 1 := by simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8791 p hg
    simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8793 (p : Pattern) (guard : d1165 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1164 p = 1 := by simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8794 (p : Pattern) (guard : d1166 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1165 p = 1 := by simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8793 p hg
    simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8795 (p : Pattern) (guard : d1167 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1166 p = 1 := by simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8796 (p : Pattern) (guard : d1168 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8795 p hg
    simpa only [d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8797 (p : Pattern) (guard : d1171 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1157 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8785 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8798 (p : Pattern) (guard : d1172 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1161 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8789 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8799 (p : Pattern) (guard : d1173 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8797 p hg
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1172 p = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8800 (p : Pattern) (guard : d1174 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8799 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8801 (p : Pattern) (guard : d1175 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8800 p hg
    simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8802 (p : Pattern) (guard : d1176 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8801 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8803 (p : Pattern) (guard : d1177 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8802 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8804 (p : Pattern) (guard : d1178 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8795 p hg
    simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1177 p = 1 := by simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8803 p hg
    simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8805 (p : Pattern) (guard : d1179 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d1168 p = 1 := by simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8796 p hg
    simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1178 p = 1 := by simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8804 p hg
    simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8806 (p : Pattern) (guard : d1180 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d1179 p = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8805 p hg
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8807 (p : Pattern) (guard : d53733 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d1180 p = 1 := by simpa only [d53733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8806 p hg
    simpa only [d53733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8808 (p : Pattern) (guard : d53734 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53733 p = 1 := by simpa only [d53734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8807 p hg
    simpa only [d53734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8809 (p : Pattern) (guard : d820 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8540 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8810 (p : Pattern) (guard : d821 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8809 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8541 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8811 (p : Pattern) (guard : d822 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8810 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8812 (p : Pattern) (guard : d823 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8811 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8813 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8814 (p : Pattern) (guard : d1084 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8813 p hg
    simpa only [d1084, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8179 p hg
    simpa only [d1084, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8815 (p : Pattern) (guard : d1085 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8814 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8816 (p : Pattern) (guard : d1086 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8815 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8817 (p : Pattern) (guard : d1087 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8816 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8818 (p : Pattern) (guard : d1088 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8542 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8817 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8819 (p : Pattern) (guard : d1089 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8818 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8820 (p : Pattern) (guard : d1090 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8812 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8819 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8821 (p : Pattern) (guard : d825 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8345 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8822 (p : Pattern) (guard : d826 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8540 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8821 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8823 (p : Pattern) (guard : d827 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8822 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8547 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8824 (p : Pattern) (guard : d828 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8823 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8825 (p : Pattern) (guard : d829 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8824 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8826 (p : Pattern) (guard : d830 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8825 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8550 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8827 (p : Pattern) (guard : d1091 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8820 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8826 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8828 (p : Pattern) (guard : d1092 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8827 p hg
    simpa only [d1092, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1092, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8829 (p : Pattern) (guard : d1093 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8816 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8006 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8830 (p : Pattern) (guard : d1094 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8348 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8831 (p : Pattern) (guard : d1095 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8830 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8832 (p : Pattern) (guard : d1096 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8819 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8833 (p : Pattern) (guard : d1097 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8832 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8551 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8834 (p : Pattern) (guard : d1098 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8833 p hg
    simpa only [d1098, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1098, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8835 (p : Pattern) (guard : d1099 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8828 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8834 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8836 (p : Pattern) (guard : d1100 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8835 p hg
    simpa only [d1100, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1100, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8837 (p : Pattern) (guard : d1101 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8836 p hg
    simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8838 (p : Pattern) (guard : d1102 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8837 p hg
    simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8839 (p : Pattern) (guard : d1103 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8838 p hg
    simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8840 (p : Pattern) (guard : d1104 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8183 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8007 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8841 (p : Pattern) (guard : d1105 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8840 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8842 (p : Pattern) (guard : d1106 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8841 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8843 (p : Pattern) (guard : d1107 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8842 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8186 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8844 (p : Pattern) (guard : d1108 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8843 p hg
    simpa only [d1108, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1108, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8845 (p : Pattern) (guard : d1109 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8834 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8844 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8846 (p : Pattern) (guard : d1110 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8845 p hg
    simpa only [d1110, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1110, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8847 (p : Pattern) (guard : d1111 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8846 p hg
    simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8848 (p : Pattern) (guard : d1112 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8849 (p : Pattern) (guard : d1113 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8848 p hg
    simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8850 (p : Pattern) (guard : d1114 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8849 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8851 (p : Pattern) (guard : d1115 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8007 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8852 (p : Pattern) (guard : d1116 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8853 (p : Pattern) (guard : d1117 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8852 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8009 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8854 (p : Pattern) (guard : d1118 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8853 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8855 (p : Pattern) (guard : d1119 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8854 p hg
    simpa only [d1119, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1119, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8856 (p : Pattern) (guard : d1120 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8844 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8855 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8857 (p : Pattern) (guard : d1121 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8856 p hg
    simpa only [d1121, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1121, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8858 (p : Pattern) (guard : d1122 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8857 p hg
    simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8859 (p : Pattern) (guard : d1123 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8858 p hg
    simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8860 (p : Pattern) (guard : d1124 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8859 p hg
    simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8861 (p : Pattern) (guard : d1125 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8849 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8860 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8862 (p : Pattern) (guard : d1126 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1114 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8850 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8861 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8863 (p : Pattern) (guard : d1127 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8860 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8864 (p : Pattern) (guard : d1128 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8861 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1127 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8863 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8865 (p : Pattern) (guard : d1129 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8862 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1128 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8864 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8866 (p : Pattern) (guard : d1130 p = 1) : d47756 p ≤ (-2 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1130, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d1130, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1129 p = 1 := by simpa only [d1130, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8865 p hg
    simpa only [d1130, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8867 (p : Pattern) (guard : d1131 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1131, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d1131, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1130 p = 1 := by simpa only [d1131, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8866 p hg
    simpa only [d1131, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8868 (p : Pattern) (guard : d1132 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8852 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8869 (p : Pattern) (guard : d1133 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8868 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8870 (p : Pattern) (guard : d1134 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8869 p hg
    simpa only [d1134, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1134, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8871 (p : Pattern) (guard : d1135 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8870 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8014 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8872 (p : Pattern) (guard : d1136 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8871 p hg
    simpa only [d1136, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1136, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8873 (p : Pattern) (guard : d1137 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1136 p = 1 := by simpa only [d1137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8872 p hg
    simpa only [d1137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8874 (p : Pattern) (guard : d1138 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1138, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1138, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1137 p = 1 := by simpa only [d1138, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8873 p hg
    simpa only [d1138, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8875 (p : Pattern) (guard : d1139 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1138 p = 1 := by simpa only [d1139, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8874 p hg
    simpa only [d1139, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1139, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1139, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8876 (p : Pattern) (guard : d1140 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1139 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8875 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8877 (p : Pattern) (guard : d1141 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8863 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1140 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8876 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8878 (p : Pattern) (guard : d1142 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1128 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8864 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1141 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8877 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8879 (p : Pattern) (guard : d1143 p = 1) : d47756 p ≤ (-2 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1143, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d1143, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1142 p = 1 := by simpa only [d1143, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8878 p hg
    simpa only [d1143, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8880 (p : Pattern) (guard : d1144 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1144, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d1144, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1143 p = 1 := by simpa only [d1144, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8879 p hg
    simpa only [d1144, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8881 (p : Pattern) (guard : d1145 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1131 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8867 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1144 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8880 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8882 (p : Pattern) (guard : d1146 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1144 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8880 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8883 (p : Pattern) (guard : d1147 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1145 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8881 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1146 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8882 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8884 (p : Pattern) (guard : d1148 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1147 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8883 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8885 (p : Pattern) (guard : d1149 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d1149, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8884 p hg
    simpa only [d1149, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1149, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d1149, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8886 (p : Pattern) (guard : d1150 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d1150, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1149 p = 1 := by simpa only [d1150, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8885 p hg
    simpa only [d1150, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8887 (p : Pattern) (guard : d1151 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1146 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8882 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8888 (p : Pattern) (guard : d1152 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8887 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8889 (p : Pattern) (guard : d1153 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1152 p = 1 := by simpa only [d1153, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8888 p hg
    simpa only [d1153, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1153, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d1153, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8890 (p : Pattern) (guard : d1154 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1154, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d1154, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1153 p = 1 := by simpa only [d1154, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8889 p hg
    simpa only [d1154, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8891 (p : Pattern) (guard : d1155 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8886 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1154 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8890 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8892 (p : Pattern) (guard : d1156 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1155 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8891 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8893 (p : Pattern) (guard : d1157 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1156 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8892 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8894 (p : Pattern) (guard : d1171 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1157 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8893 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8895 (p : Pattern) (guard : d1159 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1154 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8890 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8896 (p : Pattern) (guard : d1160 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1159 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8895 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8897 (p : Pattern) (guard : d1161 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1160 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8896 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8898 (p : Pattern) (guard : d1172 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1161 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8897 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8899 (p : Pattern) (guard : d1173 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8894 p hg
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1172 p = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8898 p hg
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8900 (p : Pattern) (guard : d1174 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8899 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8901 (p : Pattern) (guard : d1175 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8900 p hg
    simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8902 (p : Pattern) (guard : d1176 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8901 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8903 (p : Pattern) (guard : d1177 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8902 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8904 (p : Pattern) (guard : d53735 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53735, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53735, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1177 p = 1 := by simpa only [d53735, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8903 p hg
    simpa only [d53735, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8905 (p : Pattern) (guard : d53736 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53735 p = 1 := by simpa only [d53736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8904 p hg
    simpa only [d53736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8906 (p : Pattern) (guard : d53737 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53736 p = 1 := by simpa only [d53737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8905 p hg
    simpa only [d53737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8907 (p : Pattern) (guard : d53738 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53737 p = 1 := by simpa only [d53738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8906 p hg
    simpa only [d53738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8908 (p : Pattern) (guard : d53739 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53738 p = 1 := by simpa only [d53739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8907 p hg
    simpa only [d53739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8909 (p : Pattern) (guard : d53740 p = 1) : d47768 p ≤ (-2 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53734 p = 1 := by simpa only [d53740, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8808 p hg
    simpa only [d53740, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53739 p = 1 := by simpa only [d53740, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8908 p hg
    simpa only [d53740, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8910 (p : Pattern) (guard : d820 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8605 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8911 (p : Pattern) (guard : d821 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8910 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8606 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8912 (p : Pattern) (guard : d822 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8911 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8913 (p : Pattern) (guard : d823 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8914 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8915 (p : Pattern) (guard : d1084 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d1084, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8221 p hg
    simpa only [d1084, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8916 (p : Pattern) (guard : d1085 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8915 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8917 (p : Pattern) (guard : d1086 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8916 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8918 (p : Pattern) (guard : d1087 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8917 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8919 (p : Pattern) (guard : d1088 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8607 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8918 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8920 (p : Pattern) (guard : d1089 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8919 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8921 (p : Pattern) (guard : d1090 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8913 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8920 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8922 (p : Pattern) (guard : d825 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8396 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8923 (p : Pattern) (guard : d826 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8605 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8922 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8924 (p : Pattern) (guard : d827 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8923 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8612 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8925 (p : Pattern) (guard : d828 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8924 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8926 (p : Pattern) (guard : d829 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8925 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8927 (p : Pattern) (guard : d830 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8926 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8615 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8928 (p : Pattern) (guard : d1091 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8921 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8927 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8929 (p : Pattern) (guard : d1092 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8928 p hg
    simpa only [d1092, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1092, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8930 (p : Pattern) (guard : d1093 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8917 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8061 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8931 (p : Pattern) (guard : d1094 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8399 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8930 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8932 (p : Pattern) (guard : d1095 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8931 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8933 (p : Pattern) (guard : d1096 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8920 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8932 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8934 (p : Pattern) (guard : d1097 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8933 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8616 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8935 (p : Pattern) (guard : d1098 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8934 p hg
    simpa only [d1098, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1098, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8936 (p : Pattern) (guard : d1099 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8929 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8935 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8937 (p : Pattern) (guard : d1380 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1380, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d1380, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1099 p = 1 := by simpa only [d1380, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8936 p hg
    simpa only [d1380, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8938 (p : Pattern) (guard : d1100 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8727 p hg
    simpa only [d1100, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1100, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8939 (p : Pattern) (guard : d1381 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1380 p = 1 := by simpa only [d1381, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8937 p hg
    simpa only [d1381, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1100 p = 1 := by simpa only [d1381, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8938 p hg
    simpa only [d1381, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8940 (p : Pattern) (guard : d820 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8623 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8941 (p : Pattern) (guard : d821 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8940 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8624 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8942 (p : Pattern) (guard : d822 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8941 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8943 (p : Pattern) (guard : d823 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8942 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8944 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8945 (p : Pattern) (guard : d1084 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8944 p hg
    simpa only [d1084, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8237 p hg
    simpa only [d1084, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8946 (p : Pattern) (guard : d1085 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8945 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8947 (p : Pattern) (guard : d1086 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8946 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8948 (p : Pattern) (guard : d1087 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8947 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8949 (p : Pattern) (guard : d1088 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8625 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8948 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8950 (p : Pattern) (guard : d1089 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8949 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8951 (p : Pattern) (guard : d1090 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8943 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8950 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8952 (p : Pattern) (guard : d825 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8412 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8953 (p : Pattern) (guard : d826 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8623 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8952 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8954 (p : Pattern) (guard : d827 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8953 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8630 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8955 (p : Pattern) (guard : d828 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8954 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8956 (p : Pattern) (guard : d829 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8955 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8957 (p : Pattern) (guard : d830 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8956 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8633 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8958 (p : Pattern) (guard : d1091 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8951 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8957 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8959 (p : Pattern) (guard : d1092 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8958 p hg
    simpa only [d1092, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1092, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8960 (p : Pattern) (guard : d1093 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8947 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8079 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8961 (p : Pattern) (guard : d1094 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8960 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8962 (p : Pattern) (guard : d1095 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8961 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8963 (p : Pattern) (guard : d1096 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8950 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8962 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8964 (p : Pattern) (guard : d1097 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8963 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8634 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8965 (p : Pattern) (guard : d1098 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8964 p hg
    simpa only [d1098, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1098, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8966 (p : Pattern) (guard : d1099 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8959 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8965 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8967 (p : Pattern) (guard : d1100 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8966 p hg
    simpa only [d1100, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1100, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8968 (p : Pattern) (guard : d1101 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8967 p hg
    simpa only [d1101, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1101, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8969 (p : Pattern) (guard : d1382 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1381 p = 1 := by simpa only [d1382, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8939 p hg
    simpa only [d1382, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1382, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8968 p hg
    simpa only [d1382, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8970 (p : Pattern) (guard : d1383 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1382 p = 1 := by simpa only [d1383, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8969 p hg
    simpa only [d1383, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1383, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1383, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8971 (p : Pattern) (guard : d1104 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8225 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8062 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8972 (p : Pattern) (guard : d1105 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8971 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8973 (p : Pattern) (guard : d1106 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8932 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8972 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8974 (p : Pattern) (guard : d1107 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8973 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8228 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8975 (p : Pattern) (guard : d1108 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8974 p hg
    simpa only [d1108, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1108, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8976 (p : Pattern) (guard : d1109 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8935 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8977 (p : Pattern) (guard : d1385 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1385, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d1385, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1109 p = 1 := by simpa only [d1385, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8976 p hg
    simpa only [d1385, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8978 (p : Pattern) (guard : d1110 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8737 p hg
    simpa only [d1110, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1110, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8979 (p : Pattern) (guard : d1386 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1385 p = 1 := by simpa only [d1386, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8977 p hg
    simpa only [d1386, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1110 p = 1 := by simpa only [d1386, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8978 p hg
    simpa only [d1386, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8980 (p : Pattern) (guard : d1104 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8241 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8080 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8981 (p : Pattern) (guard : d1105 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8980 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8982 (p : Pattern) (guard : d1106 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8962 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8981 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8983 (p : Pattern) (guard : d1107 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8982 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8244 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8984 (p : Pattern) (guard : d1108 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8983 p hg
    simpa only [d1108, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1108, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8985 (p : Pattern) (guard : d1109 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8965 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8984 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8986 (p : Pattern) (guard : d1110 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8985 p hg
    simpa only [d1110, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1110, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8987 (p : Pattern) (guard : d1111 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8986 p hg
    simpa only [d1111, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1111, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8988 (p : Pattern) (guard : d1387 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1386 p = 1 := by simpa only [d1387, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8979 p hg
    simpa only [d1387, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1387, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8987 p hg
    simpa only [d1387, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8989 (p : Pattern) (guard : d1388 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1387 p = 1 := by simpa only [d1388, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8988 p hg
    simpa only [d1388, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1388, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1388, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8990 (p : Pattern) (guard : d1389 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1383 p = 1 := by simpa only [d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8970 p hg
    simpa only [d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1388 p = 1 := by simpa only [d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8989 p hg
    simpa only [d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8991 (p : Pattern) (guard : d1115 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8062 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8992 (p : Pattern) (guard : d1116 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8991 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8993 (p : Pattern) (guard : d1117 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8992 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8994 (p : Pattern) (guard : d1118 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8993 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8065 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8995 (p : Pattern) (guard : d1119 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8994 p hg
    simpa only [d1119, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1119, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8996 (p : Pattern) (guard : d1120 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8995 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8997 (p : Pattern) (guard : d1391 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1391, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d1391, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1120 p = 1 := by simpa only [d1391, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8996 p hg
    simpa only [d1391, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8998 (p : Pattern) (guard : d1121 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8748 p hg
    simpa only [d1121, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1121, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8999 (p : Pattern) (guard : d1392 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1391 p = 1 := by simpa only [d1392, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8997 p hg
    simpa only [d1392, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1121 p = 1 := by simpa only [d1392, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8998 p hg
    simpa only [d1392, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
