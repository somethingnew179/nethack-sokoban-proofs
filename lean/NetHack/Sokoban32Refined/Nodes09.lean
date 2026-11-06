/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1080 (p : Pattern) : Int := if p 86 then d1079 p else d1076 p
theorem agree1080 (p q : Pattern) (h : Agree support p q) : d1080 p = d1080 q := by
  simp only [d1080, h 86 (by decide), agree1079 p q h, agree1076 p q h]
theorem nonnegative1080 (p : Pattern) : 0 ≤ d1080 p :=
  nonnegative_ite (p 86) (nonnegative1079 p) (nonnegative1076 p)
def d1081 (p : Pattern) : Int := if p 112 then d80 p else d77 p
theorem agree1081 (p q : Pattern) (h : Agree support p q) : d1081 p = d1081 q := by
  simp only [d1081, h 112 (by decide), agree80 p q h, agree77 p q h]
theorem nonnegative1081 (p : Pattern) : 0 ≤ d1081 p :=
  nonnegative_ite (p 112) (nonnegative80 p) (nonnegative77 p)
def d1082 (p : Pattern) : Int := if p 106 then d1081 p else d1074 p
theorem agree1082 (p q : Pattern) (h : Agree support p q) : d1082 p = d1082 q := by
  simp only [d1082, h 106 (by decide), agree1081 p q h, agree1074 p q h]
theorem nonnegative1082 (p : Pattern) : 0 ≤ d1082 p :=
  nonnegative_ite (p 106) (nonnegative1081 p) (nonnegative1074 p)
def d1083 (p : Pattern) : Int := if p 112 then d112 p else d77 p
theorem agree1083 (p q : Pattern) (h : Agree support p q) : d1083 p = d1083 q := by
  simp only [d1083, h 112 (by decide), agree112 p q h, agree77 p q h]
theorem nonnegative1083 (p : Pattern) : 0 ≤ d1083 p :=
  nonnegative_ite (p 112) (nonnegative112 p) (nonnegative77 p)
def d1084 (p : Pattern) : Int := if p 106 then d1083 p else d1077 p
theorem agree1084 (p q : Pattern) (h : Agree support p q) : d1084 p = d1084 q := by
  simp only [d1084, h 106 (by decide), agree1083 p q h, agree1077 p q h]
theorem nonnegative1084 (p : Pattern) : 0 ≤ d1084 p :=
  nonnegative_ite (p 106) (nonnegative1083 p) (nonnegative1077 p)
def d1085 (p : Pattern) : Int := if p 86 then d1084 p else d1082 p
theorem agree1085 (p q : Pattern) (h : Agree support p q) : d1085 p = d1085 q := by
  simp only [d1085, h 86 (by decide), agree1084 p q h, agree1082 p q h]
theorem nonnegative1085 (p : Pattern) : 0 ≤ d1085 p :=
  nonnegative_ite (p 86) (nonnegative1084 p) (nonnegative1082 p)
def d1086 (p : Pattern) : Int := if p 80 then d1085 p else d1080 p
theorem agree1086 (p q : Pattern) (h : Agree support p q) : d1086 p = d1086 q := by
  simp only [d1086, h 80 (by decide), agree1085 p q h, agree1080 p q h]
theorem nonnegative1086 (p : Pattern) : 0 ≤ d1086 p :=
  nonnegative_ite (p 80) (nonnegative1085 p) (nonnegative1080 p)
def d1087 (p : Pattern) : Int := if p 139 then d1 p else d0 p
theorem agree1087 (p q : Pattern) (h : Agree support p q) : d1087 p = d1087 q := by
  simp only [d1087, h 139 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative1087 (p : Pattern) : 0 ≤ d1087 p :=
  nonnegative_ite (p 139) (nonnegative1 p) (nonnegative0 p)
def d1088 (p : Pattern) : Int := if p 139 then d0 p else d1 p
theorem agree1088 (p q : Pattern) (h : Agree support p q) : d1088 p = d1088 q := by
  simp only [d1088, h 139 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative1088 (p : Pattern) : 0 ≤ d1088 p :=
  nonnegative_ite (p 139) (nonnegative0 p) (nonnegative1 p)
def d1089 (p : Pattern) : Int := if p 112 then d0 p else d1088 p
theorem agree1089 (p q : Pattern) (h : Agree support p q) : d1089 p = d1089 q := by
  simp only [d1089, h 112 (by decide), agree0 p q h, agree1088 p q h]
theorem nonnegative1089 (p : Pattern) : 0 ≤ d1089 p :=
  nonnegative_ite (p 112) (nonnegative0 p) (nonnegative1088 p)
def d1090 (p : Pattern) : Int := if p 113 then d856 p else d0 p
theorem agree1090 (p q : Pattern) (h : Agree support p q) : d1090 p = d1090 q := by
  simp only [d1090, h 113 (by decide), agree856 p q h, agree0 p q h]
theorem nonnegative1090 (p : Pattern) : 0 ≤ d1090 p :=
  nonnegative_ite (p 113) (nonnegative856 p) (nonnegative0 p)
def d1091 (p : Pattern) : Int := if p 113 then d857 p else d1 p
theorem agree1091 (p q : Pattern) (h : Agree support p q) : d1091 p = d1091 q := by
  simp only [d1091, h 113 (by decide), agree857 p q h, agree1 p q h]
theorem nonnegative1091 (p : Pattern) : 0 ≤ d1091 p :=
  nonnegative_ite (p 113) (nonnegative857 p) (nonnegative1 p)
def d1092 (p : Pattern) : Int := if p 138 then d0 p else d1088 p
theorem agree1092 (p q : Pattern) (h : Agree support p q) : d1092 p = d1092 q := by
  simp only [d1092, h 138 (by decide), agree0 p q h, agree1088 p q h]
theorem nonnegative1092 (p : Pattern) : 0 ≤ d1092 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative1088 p)
def d1093 (p : Pattern) : Int := if p 113 then d1092 p else d1088 p
theorem agree1093 (p q : Pattern) (h : Agree support p q) : d1093 p = d1093 q := by
  simp only [d1093, h 113 (by decide), agree1092 p q h, agree1088 p q h]
theorem nonnegative1093 (p : Pattern) : 0 ≤ d1093 p :=
  nonnegative_ite (p 113) (nonnegative1092 p) (nonnegative1088 p)
def d1094 (p : Pattern) : Int := if p 112 then d0 p else d1093 p
theorem agree1094 (p q : Pattern) (h : Agree support p q) : d1094 p = d1094 q := by
  simp only [d1094, h 112 (by decide), agree0 p q h, agree1093 p q h]
theorem nonnegative1094 (p : Pattern) : 0 ≤ d1094 p :=
  nonnegative_ite (p 112) (nonnegative0 p) (nonnegative1093 p)
def d1095 (p : Pattern) : Int := if p 113 then d0 p else d1088 p
theorem agree1095 (p q : Pattern) (h : Agree support p q) : d1095 p = d1095 q := by
  simp only [d1095, h 113 (by decide), agree0 p q h, agree1088 p q h]
theorem nonnegative1095 (p : Pattern) : 0 ≤ d1095 p :=
  nonnegative_ite (p 113) (nonnegative0 p) (nonnegative1088 p)
def d1096 (p : Pattern) : Int := if p 113 then d0 p else d1087 p
theorem agree1096 (p q : Pattern) (h : Agree support p q) : d1096 p = d1096 q := by
  simp only [d1096, h 113 (by decide), agree0 p q h, agree1087 p q h]
theorem nonnegative1096 (p : Pattern) : 0 ≤ d1096 p :=
  nonnegative_ite (p 113) (nonnegative0 p) (nonnegative1087 p)
def d1097 (p : Pattern) : Int := if p 134 then d20 p else d8 p
theorem agree1097 (p q : Pattern) (h : Agree support p q) : d1097 p = d1097 q := by
  simp only [d1097, h 134 (by decide), agree20 p q h, agree8 p q h]
theorem nonnegative1097 (p : Pattern) : 0 ≤ d1097 p :=
  nonnegative_ite (p 134) (nonnegative20 p) (nonnegative8 p)
def d1098 (p : Pattern) : Int := if p 133 then d1097 p else d8 p
theorem agree1098 (p q : Pattern) (h : Agree support p q) : d1098 p = d1098 q := by
  simp only [d1098, h 133 (by decide), agree1097 p q h, agree8 p q h]
theorem nonnegative1098 (p : Pattern) : 0 ≤ d1098 p :=
  nonnegative_ite (p 133) (nonnegative1097 p) (nonnegative8 p)
def d1099 (p : Pattern) : Int := if p 134 then d33 p else d8 p
theorem agree1099 (p q : Pattern) (h : Agree support p q) : d1099 p = d1099 q := by
  simp only [d1099, h 134 (by decide), agree33 p q h, agree8 p q h]
theorem nonnegative1099 (p : Pattern) : 0 ≤ d1099 p :=
  nonnegative_ite (p 134) (nonnegative33 p) (nonnegative8 p)
def d1100 (p : Pattern) : Int := if p 134 then d20 p else d38 p
theorem agree1100 (p q : Pattern) (h : Agree support p q) : d1100 p = d1100 q := by
  simp only [d1100, h 134 (by decide), agree20 p q h, agree38 p q h]
theorem nonnegative1100 (p : Pattern) : 0 ≤ d1100 p :=
  nonnegative_ite (p 134) (nonnegative20 p) (nonnegative38 p)
def d1101 (p : Pattern) : Int := if p 133 then d1100 p else d1099 p
theorem agree1101 (p q : Pattern) (h : Agree support p q) : d1101 p = d1101 q := by
  simp only [d1101, h 133 (by decide), agree1100 p q h, agree1099 p q h]
theorem nonnegative1101 (p : Pattern) : 0 ≤ d1101 p :=
  nonnegative_ite (p 133) (nonnegative1100 p) (nonnegative1099 p)
def d1102 (p : Pattern) : Int := if p 132 then d1101 p else d1098 p
theorem agree1102 (p q : Pattern) (h : Agree support p q) : d1102 p = d1102 q := by
  simp only [d1102, h 132 (by decide), agree1101 p q h, agree1098 p q h]
theorem nonnegative1102 (p : Pattern) : 0 ≤ d1102 p :=
  nonnegative_ite (p 132) (nonnegative1101 p) (nonnegative1098 p)
def d1103 (p : Pattern) : Int := if p 134 then d24 p else d40 p
theorem agree1103 (p q : Pattern) (h : Agree support p q) : d1103 p = d1103 q := by
  simp only [d1103, h 134 (by decide), agree24 p q h, agree40 p q h]
theorem nonnegative1103 (p : Pattern) : 0 ≤ d1103 p :=
  nonnegative_ite (p 134) (nonnegative24 p) (nonnegative40 p)
def d1104 (p : Pattern) : Int := if p 133 then d1103 p else d1097 p
theorem agree1104 (p q : Pattern) (h : Agree support p q) : d1104 p = d1104 q := by
  simp only [d1104, h 133 (by decide), agree1103 p q h, agree1097 p q h]
theorem nonnegative1104 (p : Pattern) : 0 ≤ d1104 p :=
  nonnegative_ite (p 133) (nonnegative1103 p) (nonnegative1097 p)
def d1105 (p : Pattern) : Int := if p 132 then d1104 p else d1098 p
theorem agree1105 (p q : Pattern) (h : Agree support p q) : d1105 p = d1105 q := by
  simp only [d1105, h 132 (by decide), agree1104 p q h, agree1098 p q h]
theorem nonnegative1105 (p : Pattern) : 0 ≤ d1105 p :=
  nonnegative_ite (p 132) (nonnegative1104 p) (nonnegative1098 p)
def d1106 (p : Pattern) : Int := if p 106 then d1105 p else d1102 p
theorem agree1106 (p q : Pattern) (h : Agree support p q) : d1106 p = d1106 q := by
  simp only [d1106, h 106 (by decide), agree1105 p q h, agree1102 p q h]
theorem nonnegative1106 (p : Pattern) : 0 ≤ d1106 p :=
  nonnegative_ite (p 106) (nonnegative1105 p) (nonnegative1102 p)
def d1107 (p : Pattern) : Int := if p 134 then d24 p else d14 p
theorem agree1107 (p q : Pattern) (h : Agree support p q) : d1107 p = d1107 q := by
  simp only [d1107, h 134 (by decide), agree24 p q h, agree14 p q h]
theorem nonnegative1107 (p : Pattern) : 0 ≤ d1107 p :=
  nonnegative_ite (p 134) (nonnegative24 p) (nonnegative14 p)
def d1108 (p : Pattern) : Int := if p 133 then d1107 p else d14 p
theorem agree1108 (p q : Pattern) (h : Agree support p q) : d1108 p = d1108 q := by
  simp only [d1108, h 133 (by decide), agree1107 p q h, agree14 p q h]
theorem nonnegative1108 (p : Pattern) : 0 ≤ d1108 p :=
  nonnegative_ite (p 133) (nonnegative1107 p) (nonnegative14 p)
def d1109 (p : Pattern) : Int := if p 133 then d1103 p else d1107 p
theorem agree1109 (p q : Pattern) (h : Agree support p q) : d1109 p = d1109 q := by
  simp only [d1109, h 133 (by decide), agree1103 p q h, agree1107 p q h]
theorem nonnegative1109 (p : Pattern) : 0 ≤ d1109 p :=
  nonnegative_ite (p 133) (nonnegative1103 p) (nonnegative1107 p)
def d1110 (p : Pattern) : Int := if p 132 then d1109 p else d1108 p
theorem agree1110 (p q : Pattern) (h : Agree support p q) : d1110 p = d1110 q := by
  simp only [d1110, h 132 (by decide), agree1109 p q h, agree1108 p q h]
theorem nonnegative1110 (p : Pattern) : 0 ≤ d1110 p :=
  nonnegative_ite (p 132) (nonnegative1109 p) (nonnegative1108 p)
def d1111 (p : Pattern) : Int := if p 112 then d1110 p else d1102 p
theorem agree1111 (p q : Pattern) (h : Agree support p q) : d1111 p = d1111 q := by
  simp only [d1111, h 112 (by decide), agree1110 p q h, agree1102 p q h]
theorem nonnegative1111 (p : Pattern) : 0 ≤ d1111 p :=
  nonnegative_ite (p 112) (nonnegative1110 p) (nonnegative1102 p)
def d1112 (p : Pattern) : Int := if p 133 then d2 p else d1107 p
theorem agree1112 (p q : Pattern) (h : Agree support p q) : d1112 p = d1112 q := by
  simp only [d1112, h 133 (by decide), agree2 p q h, agree1107 p q h]
theorem nonnegative1112 (p : Pattern) : 0 ≤ d1112 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1107 p)
def d1113 (p : Pattern) : Int := if p 132 then d1112 p else d1108 p
theorem agree1113 (p q : Pattern) (h : Agree support p q) : d1113 p = d1113 q := by
  simp only [d1113, h 132 (by decide), agree1112 p q h, agree1108 p q h]
theorem nonnegative1113 (p : Pattern) : 0 ≤ d1113 p :=
  nonnegative_ite (p 132) (nonnegative1112 p) (nonnegative1108 p)
def d1114 (p : Pattern) : Int := if p 112 then d1113 p else d1105 p
theorem agree1114 (p q : Pattern) (h : Agree support p q) : d1114 p = d1114 q := by
  simp only [d1114, h 112 (by decide), agree1113 p q h, agree1105 p q h]
theorem nonnegative1114 (p : Pattern) : 0 ≤ d1114 p :=
  nonnegative_ite (p 112) (nonnegative1113 p) (nonnegative1105 p)
def d1115 (p : Pattern) : Int := if p 106 then d1114 p else d1111 p
theorem agree1115 (p q : Pattern) (h : Agree support p q) : d1115 p = d1115 q := by
  simp only [d1115, h 106 (by decide), agree1114 p q h, agree1111 p q h]
theorem nonnegative1115 (p : Pattern) : 0 ≤ d1115 p :=
  nonnegative_ite (p 106) (nonnegative1114 p) (nonnegative1111 p)
def d1116 (p : Pattern) : Int := if p 86 then d1115 p else d1106 p
theorem agree1116 (p q : Pattern) (h : Agree support p q) : d1116 p = d1116 q := by
  simp only [d1116, h 86 (by decide), agree1115 p q h, agree1106 p q h]
theorem nonnegative1116 (p : Pattern) : 0 ≤ d1116 p :=
  nonnegative_ite (p 86) (nonnegative1115 p) (nonnegative1106 p)
def d1117 (p : Pattern) : Int := if p 113 then d2 p else d1113 p
theorem agree1117 (p q : Pattern) (h : Agree support p q) : d1117 p = d1117 q := by
  simp only [d1117, h 113 (by decide), agree2 p q h, agree1113 p q h]
theorem nonnegative1117 (p : Pattern) : 0 ≤ d1117 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1113 p)
def d1118 (p : Pattern) : Int := if p 112 then d1117 p else d1105 p
theorem agree1118 (p q : Pattern) (h : Agree support p q) : d1118 p = d1118 q := by
  simp only [d1118, h 112 (by decide), agree1117 p q h, agree1105 p q h]
theorem nonnegative1118 (p : Pattern) : 0 ≤ d1118 p :=
  nonnegative_ite (p 112) (nonnegative1117 p) (nonnegative1105 p)
def d1119 (p : Pattern) : Int := if p 106 then d1118 p else d1111 p
theorem agree1119 (p q : Pattern) (h : Agree support p q) : d1119 p = d1119 q := by
  simp only [d1119, h 106 (by decide), agree1118 p q h, agree1111 p q h]
theorem nonnegative1119 (p : Pattern) : 0 ≤ d1119 p :=
  nonnegative_ite (p 106) (nonnegative1118 p) (nonnegative1111 p)
def d1120 (p : Pattern) : Int := if p 86 then d1119 p else d1106 p
theorem agree1120 (p q : Pattern) (h : Agree support p q) : d1120 p = d1120 q := by
  simp only [d1120, h 86 (by decide), agree1119 p q h, agree1106 p q h]
theorem nonnegative1120 (p : Pattern) : 0 ≤ d1120 p :=
  nonnegative_ite (p 86) (nonnegative1119 p) (nonnegative1106 p)
def d1121 (p : Pattern) : Int := if p 80 then d1120 p else d1116 p
theorem agree1121 (p q : Pattern) (h : Agree support p q) : d1121 p = d1121 q := by
  simp only [d1121, h 80 (by decide), agree1120 p q h, agree1116 p q h]
theorem nonnegative1121 (p : Pattern) : 0 ≤ d1121 p :=
  nonnegative_ite (p 80) (nonnegative1120 p) (nonnegative1116 p)
def d1122 (p : Pattern) : Int := if p 113 then d0 p else d857 p
theorem agree1122 (p q : Pattern) (h : Agree support p q) : d1122 p = d1122 q := by
  simp only [d1122, h 113 (by decide), agree0 p q h, agree857 p q h]
theorem nonnegative1122 (p : Pattern) : 0 ≤ d1122 p :=
  nonnegative_ite (p 113) (nonnegative0 p) (nonnegative857 p)
def d1123 (p : Pattern) : Int := if p 112 then d1087 p else d0 p
theorem agree1123 (p q : Pattern) (h : Agree support p q) : d1123 p = d1123 q := by
  simp only [d1123, h 112 (by decide), agree1087 p q h, agree0 p q h]
theorem nonnegative1123 (p : Pattern) : 0 ≤ d1123 p :=
  nonnegative_ite (p 112) (nonnegative1087 p) (nonnegative0 p)
def d1124 (p : Pattern) : Int := if p 112 then d1088 p else d1 p
theorem agree1124 (p q : Pattern) (h : Agree support p q) : d1124 p = d1124 q := by
  simp only [d1124, h 112 (by decide), agree1088 p q h, agree1 p q h]
theorem nonnegative1124 (p : Pattern) : 0 ≤ d1124 p :=
  nonnegative_ite (p 112) (nonnegative1088 p) (nonnegative1 p)
def d1125 (p : Pattern) : Int := if p 113 then d0 p else d1092 p
theorem agree1125 (p q : Pattern) (h : Agree support p q) : d1125 p = d1125 q := by
  simp only [d1125, h 113 (by decide), agree0 p q h, agree1092 p q h]
theorem nonnegative1125 (p : Pattern) : 0 ≤ d1125 p :=
  nonnegative_ite (p 113) (nonnegative0 p) (nonnegative1092 p)
def d1126 (p : Pattern) : Int := if p 112 then d1125 p else d1122 p
theorem agree1126 (p q : Pattern) (h : Agree support p q) : d1126 p = d1126 q := by
  simp only [d1126, h 112 (by decide), agree1125 p q h, agree1122 p q h]
theorem nonnegative1126 (p : Pattern) : 0 ≤ d1126 p :=
  nonnegative_ite (p 112) (nonnegative1125 p) (nonnegative1122 p)
def d1127 (p : Pattern) : Int := if p 106 then d108 p else d102 p
theorem agree1127 (p q : Pattern) (h : Agree support p q) : d1127 p = d1127 q := by
  simp only [d1127, h 106 (by decide), agree108 p q h, agree102 p q h]
theorem nonnegative1127 (p : Pattern) : 0 ≤ d1127 p :=
  nonnegative_ite (p 106) (nonnegative108 p) (nonnegative102 p)
def d1128 (p : Pattern) : Int := if p 86 then d1127 p else d860 p
theorem agree1128 (p q : Pattern) (h : Agree support p q) : d1128 p = d1128 q := by
  simp only [d1128, h 86 (by decide), agree1127 p q h, agree860 p q h]
theorem nonnegative1128 (p : Pattern) : 0 ≤ d1128 p :=
  nonnegative_ite (p 86) (nonnegative1127 p) (nonnegative860 p)
def d1129 (p : Pattern) : Int := if p 106 then d112 p else d102 p
theorem agree1129 (p q : Pattern) (h : Agree support p q) : d1129 p = d1129 q := by
  simp only [d1129, h 106 (by decide), agree112 p q h, agree102 p q h]
theorem nonnegative1129 (p : Pattern) : 0 ≤ d1129 p :=
  nonnegative_ite (p 106) (nonnegative112 p) (nonnegative102 p)
def d1130 (p : Pattern) : Int := if p 86 then d1129 p else d860 p
theorem agree1130 (p q : Pattern) (h : Agree support p q) : d1130 p = d1130 q := by
  simp only [d1130, h 86 (by decide), agree1129 p q h, agree860 p q h]
theorem nonnegative1130 (p : Pattern) : 0 ≤ d1130 p :=
  nonnegative_ite (p 86) (nonnegative1129 p) (nonnegative860 p)
def d1131 (p : Pattern) : Int := if p 80 then d1130 p else d1128 p
theorem agree1131 (p q : Pattern) (h : Agree support p q) : d1131 p = d1131 q := by
  simp only [d1131, h 80 (by decide), agree1130 p q h, agree1128 p q h]
theorem nonnegative1131 (p : Pattern) : 0 ≤ d1131 p :=
  nonnegative_ite (p 80) (nonnegative1130 p) (nonnegative1128 p)
def d1132 (p : Pattern) : Int := if p 132 then d910 p else d0 p
theorem agree1132 (p q : Pattern) (h : Agree support p q) : d1132 p = d1132 q := by
  simp only [d1132, h 132 (by decide), agree910 p q h, agree0 p q h]
theorem nonnegative1132 (p : Pattern) : 0 ≤ d1132 p :=
  nonnegative_ite (p 132) (nonnegative910 p) (nonnegative0 p)
def d1133 (p : Pattern) : Int := if p 113 then d56 p else d46 p
theorem agree1133 (p q : Pattern) (h : Agree support p q) : d1133 p = d1133 q := by
  simp only [d1133, h 113 (by decide), agree56 p q h, agree46 p q h]
theorem nonnegative1133 (p : Pattern) : 0 ≤ d1133 p :=
  nonnegative_ite (p 113) (nonnegative56 p) (nonnegative46 p)
def d1134 (p : Pattern) : Int := if p 112 then d1133 p else d27 p
theorem agree1134 (p q : Pattern) (h : Agree support p q) : d1134 p = d1134 q := by
  simp only [d1134, h 112 (by decide), agree1133 p q h, agree27 p q h]
theorem nonnegative1134 (p : Pattern) : 0 ≤ d1134 p :=
  nonnegative_ite (p 112) (nonnegative1133 p) (nonnegative27 p)
def d1135 (p : Pattern) : Int := if p 113 then d88 p else d27 p
theorem agree1135 (p q : Pattern) (h : Agree support p q) : d1135 p = d1135 q := by
  simp only [d1135, h 113 (by decide), agree88 p q h, agree27 p q h]
theorem nonnegative1135 (p : Pattern) : 0 ≤ d1135 p :=
  nonnegative_ite (p 113) (nonnegative88 p) (nonnegative27 p)
def d1136 (p : Pattern) : Int := if p 112 then d99 p else d1135 p
theorem agree1136 (p q : Pattern) (h : Agree support p q) : d1136 p = d1136 q := by
  simp only [d1136, h 112 (by decide), agree99 p q h, agree1135 p q h]
theorem nonnegative1136 (p : Pattern) : 0 ≤ d1136 p :=
  nonnegative_ite (p 112) (nonnegative99 p) (nonnegative1135 p)
def d1137 (p : Pattern) : Int := if p 113 then d109 p else d99 p
theorem agree1137 (p q : Pattern) (h : Agree support p q) : d1137 p = d1137 q := by
  simp only [d1137, h 113 (by decide), agree109 p q h, agree99 p q h]
theorem nonnegative1137 (p : Pattern) : 0 ≤ d1137 p :=
  nonnegative_ite (p 113) (nonnegative109 p) (nonnegative99 p)
def d1138 (p : Pattern) : Int := if p 112 then d1137 p else d1135 p
theorem agree1138 (p q : Pattern) (h : Agree support p q) : d1138 p = d1138 q := by
  simp only [d1138, h 112 (by decide), agree1137 p q h, agree1135 p q h]
theorem nonnegative1138 (p : Pattern) : 0 ≤ d1138 p :=
  nonnegative_ite (p 112) (nonnegative1137 p) (nonnegative1135 p)
def d1139 (p : Pattern) : Int := if p 106 then d1138 p else d1136 p
theorem agree1139 (p q : Pattern) (h : Agree support p q) : d1139 p = d1139 q := by
  simp only [d1139, h 106 (by decide), agree1138 p q h, agree1136 p q h]
theorem nonnegative1139 (p : Pattern) : 0 ≤ d1139 p :=
  nonnegative_ite (p 106) (nonnegative1138 p) (nonnegative1136 p)
def d1140 (p : Pattern) : Int := if p 86 then d1139 p else d1134 p
theorem agree1140 (p q : Pattern) (h : Agree support p q) : d1140 p = d1140 q := by
  simp only [d1140, h 86 (by decide), agree1139 p q h, agree1134 p q h]
theorem nonnegative1140 (p : Pattern) : 0 ≤ d1140 p :=
  nonnegative_ite (p 86) (nonnegative1139 p) (nonnegative1134 p)
def d1141 (p : Pattern) : Int := if p 113 then d56 p else d27 p
theorem agree1141 (p q : Pattern) (h : Agree support p q) : d1141 p = d1141 q := by
  simp only [d1141, h 113 (by decide), agree56 p q h, agree27 p q h]
theorem nonnegative1141 (p : Pattern) : 0 ≤ d1141 p :=
  nonnegative_ite (p 113) (nonnegative56 p) (nonnegative27 p)
def d1142 (p : Pattern) : Int := if p 113 then d2 p else d109 p
theorem agree1142 (p q : Pattern) (h : Agree support p q) : d1142 p = d1142 q := by
  simp only [d1142, h 113 (by decide), agree2 p q h, agree109 p q h]
theorem nonnegative1142 (p : Pattern) : 0 ≤ d1142 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative109 p)
def d1143 (p : Pattern) : Int := if p 112 then d1142 p else d1141 p
theorem agree1143 (p q : Pattern) (h : Agree support p q) : d1143 p = d1143 q := by
  simp only [d1143, h 112 (by decide), agree1142 p q h, agree1141 p q h]
theorem nonnegative1143 (p : Pattern) : 0 ≤ d1143 p :=
  nonnegative_ite (p 112) (nonnegative1142 p) (nonnegative1141 p)
def d1144 (p : Pattern) : Int := if p 106 then d1143 p else d1138 p
theorem agree1144 (p q : Pattern) (h : Agree support p q) : d1144 p = d1144 q := by
  simp only [d1144, h 106 (by decide), agree1143 p q h, agree1138 p q h]
theorem nonnegative1144 (p : Pattern) : 0 ≤ d1144 p :=
  nonnegative_ite (p 106) (nonnegative1143 p) (nonnegative1138 p)
def d1145 (p : Pattern) : Int := if p 86 then d1144 p else d1134 p
theorem agree1145 (p q : Pattern) (h : Agree support p q) : d1145 p = d1145 q := by
  simp only [d1145, h 86 (by decide), agree1144 p q h, agree1134 p q h]
theorem nonnegative1145 (p : Pattern) : 0 ≤ d1145 p :=
  nonnegative_ite (p 86) (nonnegative1144 p) (nonnegative1134 p)
def d1146 (p : Pattern) : Int := if p 80 then d1145 p else d1140 p
theorem agree1146 (p q : Pattern) (h : Agree support p q) : d1146 p = d1146 q := by
  simp only [d1146, h 80 (by decide), agree1145 p q h, agree1140 p q h]
theorem nonnegative1146 (p : Pattern) : 0 ≤ d1146 p :=
  nonnegative_ite (p 80) (nonnegative1145 p) (nonnegative1140 p)
def d1147 (p : Pattern) : Int := if p 86 then d128 p else d67 p
theorem agree1147 (p q : Pattern) (h : Agree support p q) : d1147 p = d1147 q := by
  simp only [d1147, h 86 (by decide), agree128 p q h, agree67 p q h]
theorem nonnegative1147 (p : Pattern) : 0 ≤ d1147 p :=
  nonnegative_ite (p 86) (nonnegative128 p) (nonnegative67 p)
def d1148 (p : Pattern) : Int := if p 132 then d0 p else d873 p
theorem agree1148 (p q : Pattern) (h : Agree support p q) : d1148 p = d1148 q := by
  simp only [d1148, h 132 (by decide), agree0 p q h, agree873 p q h]
theorem nonnegative1148 (p : Pattern) : 0 ≤ d1148 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative873 p)
def d1149 (p : Pattern) : Int := if p 132 then d0 p else d909 p
theorem agree1149 (p q : Pattern) (h : Agree support p q) : d1149 p = d1149 q := by
  simp only [d1149, h 132 (by decide), agree0 p q h, agree909 p q h]
theorem nonnegative1149 (p : Pattern) : 0 ≤ d1149 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative909 p)
def d1150 (p : Pattern) : Int := if p 133 then d915 p else d0 p
theorem agree1150 (p q : Pattern) (h : Agree support p q) : d1150 p = d1150 q := by
  simp only [d1150, h 133 (by decide), agree915 p q h, agree0 p q h]
theorem nonnegative1150 (p : Pattern) : 0 ≤ d1150 p :=
  nonnegative_ite (p 133) (nonnegative915 p) (nonnegative0 p)
def d1151 (p : Pattern) : Int := if p 132 then d0 p else d1150 p
theorem agree1151 (p q : Pattern) (h : Agree support p q) : d1151 p = d1151 q := by
  simp only [d1151, h 132 (by decide), agree0 p q h, agree1150 p q h]
theorem nonnegative1151 (p : Pattern) : 0 ≤ d1151 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative1150 p)
def d1152 (p : Pattern) : Int := if p 113 then d53 p else d15 p
theorem agree1152 (p q : Pattern) (h : Agree support p q) : d1152 p = d1152 q := by
  simp only [d1152, h 113 (by decide), agree53 p q h, agree15 p q h]
theorem nonnegative1152 (p : Pattern) : 0 ≤ d1152 p :=
  nonnegative_ite (p 113) (nonnegative53 p) (nonnegative15 p)
def d1153 (p : Pattern) : Int := if p 112 then d1152 p else d16 p
theorem agree1153 (p q : Pattern) (h : Agree support p q) : d1153 p = d1153 q := by
  simp only [d1153, h 112 (by decide), agree1152 p q h, agree16 p q h]
theorem nonnegative1153 (p : Pattern) : 0 ≤ d1153 p :=
  nonnegative_ite (p 112) (nonnegative1152 p) (nonnegative16 p)
def d1154 (p : Pattern) : Int := if p 113 then d86 p else d16 p
theorem agree1154 (p q : Pattern) (h : Agree support p q) : d1154 p = d1154 q := by
  simp only [d1154, h 113 (by decide), agree86 p q h, agree16 p q h]
theorem nonnegative1154 (p : Pattern) : 0 ≤ d1154 p :=
  nonnegative_ite (p 113) (nonnegative86 p) (nonnegative16 p)
def d1155 (p : Pattern) : Int := if p 112 then d98 p else d1154 p
theorem agree1155 (p q : Pattern) (h : Agree support p q) : d1155 p = d1155 q := by
  simp only [d1155, h 112 (by decide), agree98 p q h, agree1154 p q h]
theorem nonnegative1155 (p : Pattern) : 0 ≤ d1155 p :=
  nonnegative_ite (p 112) (nonnegative98 p) (nonnegative1154 p)
def d1156 (p : Pattern) : Int := if p 113 then d97 p else d98 p
theorem agree1156 (p q : Pattern) (h : Agree support p q) : d1156 p = d1156 q := by
  simp only [d1156, h 113 (by decide), agree97 p q h, agree98 p q h]
theorem nonnegative1156 (p : Pattern) : 0 ≤ d1156 p :=
  nonnegative_ite (p 113) (nonnegative97 p) (nonnegative98 p)
def d1157 (p : Pattern) : Int := if p 112 then d1156 p else d1154 p
theorem agree1157 (p q : Pattern) (h : Agree support p q) : d1157 p = d1157 q := by
  simp only [d1157, h 112 (by decide), agree1156 p q h, agree1154 p q h]
theorem nonnegative1157 (p : Pattern) : 0 ≤ d1157 p :=
  nonnegative_ite (p 112) (nonnegative1156 p) (nonnegative1154 p)
def d1158 (p : Pattern) : Int := if p 106 then d1157 p else d1155 p
theorem agree1158 (p q : Pattern) (h : Agree support p q) : d1158 p = d1158 q := by
  simp only [d1158, h 106 (by decide), agree1157 p q h, agree1155 p q h]
theorem nonnegative1158 (p : Pattern) : 0 ≤ d1158 p :=
  nonnegative_ite (p 106) (nonnegative1157 p) (nonnegative1155 p)
def d1159 (p : Pattern) : Int := if p 86 then d1158 p else d1153 p
theorem agree1159 (p q : Pattern) (h : Agree support p q) : d1159 p = d1159 q := by
  simp only [d1159, h 86 (by decide), agree1158 p q h, agree1153 p q h]
theorem nonnegative1159 (p : Pattern) : 0 ≤ d1159 p :=
  nonnegative_ite (p 86) (nonnegative1158 p) (nonnegative1153 p)
def d1160 (p : Pattern) : Int := if p 113 then d53 p else d16 p
theorem agree1160 (p q : Pattern) (h : Agree support p q) : d1160 p = d1160 q := by
  simp only [d1160, h 113 (by decide), agree53 p q h, agree16 p q h]
theorem nonnegative1160 (p : Pattern) : 0 ≤ d1160 p :=
  nonnegative_ite (p 113) (nonnegative53 p) (nonnegative16 p)
def d1161 (p : Pattern) : Int := if p 113 then d2 p else d97 p
theorem agree1161 (p q : Pattern) (h : Agree support p q) : d1161 p = d1161 q := by
  simp only [d1161, h 113 (by decide), agree2 p q h, agree97 p q h]
theorem nonnegative1161 (p : Pattern) : 0 ≤ d1161 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative97 p)
def d1162 (p : Pattern) : Int := if p 112 then d1161 p else d1160 p
theorem agree1162 (p q : Pattern) (h : Agree support p q) : d1162 p = d1162 q := by
  simp only [d1162, h 112 (by decide), agree1161 p q h, agree1160 p q h]
theorem nonnegative1162 (p : Pattern) : 0 ≤ d1162 p :=
  nonnegative_ite (p 112) (nonnegative1161 p) (nonnegative1160 p)
def d1163 (p : Pattern) : Int := if p 106 then d1162 p else d1157 p
theorem agree1163 (p q : Pattern) (h : Agree support p q) : d1163 p = d1163 q := by
  simp only [d1163, h 106 (by decide), agree1162 p q h, agree1157 p q h]
theorem nonnegative1163 (p : Pattern) : 0 ≤ d1163 p :=
  nonnegative_ite (p 106) (nonnegative1162 p) (nonnegative1157 p)
def d1164 (p : Pattern) : Int := if p 86 then d1163 p else d1153 p
theorem agree1164 (p q : Pattern) (h : Agree support p q) : d1164 p = d1164 q := by
  simp only [d1164, h 86 (by decide), agree1163 p q h, agree1153 p q h]
theorem nonnegative1164 (p : Pattern) : 0 ≤ d1164 p :=
  nonnegative_ite (p 86) (nonnegative1163 p) (nonnegative1153 p)
def d1165 (p : Pattern) : Int := if p 80 then d1164 p else d1159 p
theorem agree1165 (p q : Pattern) (h : Agree support p q) : d1165 p = d1165 q := by
  simp only [d1165, h 80 (by decide), agree1164 p q h, agree1159 p q h]
theorem nonnegative1165 (p : Pattern) : 0 ≤ d1165 p :=
  nonnegative_ite (p 80) (nonnegative1164 p) (nonnegative1159 p)
def d1166 (p : Pattern) : Int := if p 159 then d1 p else d0 p
theorem agree1166 (p q : Pattern) (h : Agree support p q) : d1166 p = d1166 q := by
  simp only [d1166, h 159 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative1166 (p : Pattern) : 0 ≤ d1166 p :=
  nonnegative_ite (p 159) (nonnegative1 p) (nonnegative0 p)
def d1167 (p : Pattern) : Int := if p 159 then d0 p else d1 p
theorem agree1167 (p q : Pattern) (h : Agree support p q) : d1167 p = d1167 q := by
  simp only [d1167, h 159 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative1167 (p : Pattern) : 0 ≤ d1167 p :=
  nonnegative_ite (p 159) (nonnegative0 p) (nonnegative1 p)
def d1168 (p : Pattern) : Int := if p 132 then d0 p else d1167 p
theorem agree1168 (p q : Pattern) (h : Agree support p q) : d1168 p = d1168 q := by
  simp only [d1168, h 132 (by decide), agree0 p q h, agree1167 p q h]
theorem nonnegative1168 (p : Pattern) : 0 ≤ d1168 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative1167 p)
def d1169 (p : Pattern) : Int := if p 133 then d872 p else d0 p
theorem agree1169 (p q : Pattern) (h : Agree support p q) : d1169 p = d1169 q := by
  simp only [d1169, h 133 (by decide), agree872 p q h, agree0 p q h]
theorem nonnegative1169 (p : Pattern) : 0 ≤ d1169 p :=
  nonnegative_ite (p 133) (nonnegative872 p) (nonnegative0 p)
def d1170 (p : Pattern) : Int := if p 133 then d873 p else d1 p
theorem agree1170 (p q : Pattern) (h : Agree support p q) : d1170 p = d1170 q := by
  simp only [d1170, h 133 (by decide), agree873 p q h, agree1 p q h]
theorem nonnegative1170 (p : Pattern) : 0 ≤ d1170 p :=
  nonnegative_ite (p 133) (nonnegative873 p) (nonnegative1 p)
def d1171 (p : Pattern) : Int := if p 158 then d0 p else d1167 p
theorem agree1171 (p q : Pattern) (h : Agree support p q) : d1171 p = d1171 q := by
  simp only [d1171, h 158 (by decide), agree0 p q h, agree1167 p q h]
theorem nonnegative1171 (p : Pattern) : 0 ≤ d1171 p :=
  nonnegative_ite (p 158) (nonnegative0 p) (nonnegative1167 p)
def d1172 (p : Pattern) : Int := if p 133 then d1171 p else d1167 p
theorem agree1172 (p q : Pattern) (h : Agree support p q) : d1172 p = d1172 q := by
  simp only [d1172, h 133 (by decide), agree1171 p q h, agree1167 p q h]
theorem nonnegative1172 (p : Pattern) : 0 ≤ d1172 p :=
  nonnegative_ite (p 133) (nonnegative1171 p) (nonnegative1167 p)
def d1173 (p : Pattern) : Int := if p 132 then d0 p else d1172 p
theorem agree1173 (p q : Pattern) (h : Agree support p q) : d1173 p = d1173 q := by
  simp only [d1173, h 132 (by decide), agree0 p q h, agree1172 p q h]
theorem nonnegative1173 (p : Pattern) : 0 ≤ d1173 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative1172 p)
def d1174 (p : Pattern) : Int := if p 133 then d0 p else d1167 p
theorem agree1174 (p q : Pattern) (h : Agree support p q) : d1174 p = d1174 q := by
  simp only [d1174, h 133 (by decide), agree0 p q h, agree1167 p q h]
theorem nonnegative1174 (p : Pattern) : 0 ≤ d1174 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative1167 p)
def d1175 (p : Pattern) : Int := if p 133 then d0 p else d914 p
theorem agree1175 (p q : Pattern) (h : Agree support p q) : d1175 p = d1175 q := by
  simp only [d1175, h 133 (by decide), agree0 p q h, agree914 p q h]
theorem nonnegative1175 (p : Pattern) : 0 ≤ d1175 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative914 p)
def d1176 (p : Pattern) : Int := if p 133 then d42 p else d16 p
theorem agree1176 (p q : Pattern) (h : Agree support p q) : d1176 p = d1176 q := by
  simp only [d1176, h 133 (by decide), agree42 p q h, agree16 p q h]
theorem nonnegative1176 (p : Pattern) : 0 ≤ d1176 p :=
  nonnegative_ite (p 133) (nonnegative42 p) (nonnegative16 p)
def d1177 (p : Pattern) : Int := if p 132 then d1176 p else d16 p
theorem agree1177 (p q : Pattern) (h : Agree support p q) : d1177 p = d1177 q := by
  simp only [d1177, h 132 (by decide), agree1176 p q h, agree16 p q h]
theorem nonnegative1177 (p : Pattern) : 0 ≤ d1177 p :=
  nonnegative_ite (p 132) (nonnegative1176 p) (nonnegative16 p)
def d1178 (p : Pattern) : Int := if p 133 then d41 p else d15 p
theorem agree1178 (p q : Pattern) (h : Agree support p q) : d1178 p = d1178 q := by
  simp only [d1178, h 133 (by decide), agree41 p q h, agree15 p q h]
theorem nonnegative1178 (p : Pattern) : 0 ≤ d1178 p :=
  nonnegative_ite (p 133) (nonnegative41 p) (nonnegative15 p)
def d1179 (p : Pattern) : Int := if p 132 then d1178 p else d15 p
theorem agree1179 (p q : Pattern) (h : Agree support p q) : d1179 p = d1179 q := by
  simp only [d1179, h 132 (by decide), agree1178 p q h, agree15 p q h]
theorem nonnegative1179 (p : Pattern) : 0 ≤ d1179 p :=
  nonnegative_ite (p 132) (nonnegative1178 p) (nonnegative15 p)
def d1180 (p : Pattern) : Int := if p 133 then d62 p else d53 p
theorem agree1180 (p q : Pattern) (h : Agree support p q) : d1180 p = d1180 q := by
  simp only [d1180, h 133 (by decide), agree62 p q h, agree53 p q h]
theorem nonnegative1180 (p : Pattern) : 0 ≤ d1180 p :=
  nonnegative_ite (p 133) (nonnegative62 p) (nonnegative53 p)
def d1181 (p : Pattern) : Int := if p 132 then d1180 p else d53 p
theorem agree1181 (p q : Pattern) (h : Agree support p q) : d1181 p = d1181 q := by
  simp only [d1181, h 132 (by decide), agree1180 p q h, agree53 p q h]
theorem nonnegative1181 (p : Pattern) : 0 ≤ d1181 p :=
  nonnegative_ite (p 132) (nonnegative1180 p) (nonnegative53 p)
def d1182 (p : Pattern) : Int := if p 113 then d1181 p else d1179 p
theorem agree1182 (p q : Pattern) (h : Agree support p q) : d1182 p = d1182 q := by
  simp only [d1182, h 113 (by decide), agree1181 p q h, agree1179 p q h]
theorem nonnegative1182 (p : Pattern) : 0 ≤ d1182 p :=
  nonnegative_ite (p 113) (nonnegative1181 p) (nonnegative1179 p)
def d1183 (p : Pattern) : Int := if p 112 then d1182 p else d1177 p
theorem agree1183 (p q : Pattern) (h : Agree support p q) : d1183 p = d1183 q := by
  simp only [d1183, h 112 (by decide), agree1182 p q h, agree1177 p q h]
theorem nonnegative1183 (p : Pattern) : 0 ≤ d1183 p :=
  nonnegative_ite (p 112) (nonnegative1182 p) (nonnegative1177 p)
def d1184 (p : Pattern) : Int := if p 133 then d69 p else d16 p
theorem agree1184 (p q : Pattern) (h : Agree support p q) : d1184 p = d1184 q := by
  simp only [d1184, h 133 (by decide), agree69 p q h, agree16 p q h]
theorem nonnegative1184 (p : Pattern) : 0 ≤ d1184 p :=
  nonnegative_ite (p 133) (nonnegative69 p) (nonnegative16 p)
def d1185 (p : Pattern) : Int := if p 132 then d1184 p else d16 p
theorem agree1185 (p q : Pattern) (h : Agree support p q) : d1185 p = d1185 q := by
  simp only [d1185, h 132 (by decide), agree1184 p q h, agree16 p q h]
theorem nonnegative1185 (p : Pattern) : 0 ≤ d1185 p :=
  nonnegative_ite (p 132) (nonnegative1184 p) (nonnegative16 p)
def d1186 (p : Pattern) : Int := if p 133 then d68 p else d16 p
theorem agree1186 (p q : Pattern) (h : Agree support p q) : d1186 p = d1186 q := by
  simp only [d1186, h 133 (by decide), agree68 p q h, agree16 p q h]
theorem nonnegative1186 (p : Pattern) : 0 ≤ d1186 p :=
  nonnegative_ite (p 133) (nonnegative68 p) (nonnegative16 p)
def d1187 (p : Pattern) : Int := if p 132 then d1186 p else d16 p
theorem agree1187 (p q : Pattern) (h : Agree support p q) : d1187 p = d1187 q := by
  simp only [d1187, h 132 (by decide), agree1186 p q h, agree16 p q h]
theorem nonnegative1187 (p : Pattern) : 0 ≤ d1187 p :=
  nonnegative_ite (p 132) (nonnegative1186 p) (nonnegative16 p)
def d1188 (p : Pattern) : Int := if p 113 then d1187 p else d1185 p
theorem agree1188 (p q : Pattern) (h : Agree support p q) : d1188 p = d1188 q := by
  simp only [d1188, h 113 (by decide), agree1187 p q h, agree1185 p q h]
theorem nonnegative1188 (p : Pattern) : 0 ≤ d1188 p :=
  nonnegative_ite (p 113) (nonnegative1187 p) (nonnegative1185 p)
def d1189 (p : Pattern) : Int := if p 133 then d68 p else d15 p
theorem agree1189 (p q : Pattern) (h : Agree support p q) : d1189 p = d1189 q := by
  simp only [d1189, h 133 (by decide), agree68 p q h, agree15 p q h]
theorem nonnegative1189 (p : Pattern) : 0 ≤ d1189 p :=
  nonnegative_ite (p 133) (nonnegative68 p) (nonnegative15 p)
def d1190 (p : Pattern) : Int := if p 132 then d1189 p else d15 p
theorem agree1190 (p q : Pattern) (h : Agree support p q) : d1190 p = d1190 q := by
  simp only [d1190, h 132 (by decide), agree1189 p q h, agree15 p q h]
theorem nonnegative1190 (p : Pattern) : 0 ≤ d1190 p :=
  nonnegative_ite (p 132) (nonnegative1189 p) (nonnegative15 p)
def d1191 (p : Pattern) : Int := if p 133 then d68 p else d53 p
theorem agree1191 (p q : Pattern) (h : Agree support p q) : d1191 p = d1191 q := by
  simp only [d1191, h 133 (by decide), agree68 p q h, agree53 p q h]
theorem nonnegative1191 (p : Pattern) : 0 ≤ d1191 p :=
  nonnegative_ite (p 133) (nonnegative68 p) (nonnegative53 p)
def d1192 (p : Pattern) : Int := if p 132 then d1191 p else d53 p
theorem agree1192 (p q : Pattern) (h : Agree support p q) : d1192 p = d1192 q := by
  simp only [d1192, h 132 (by decide), agree1191 p q h, agree53 p q h]
theorem nonnegative1192 (p : Pattern) : 0 ≤ d1192 p :=
  nonnegative_ite (p 132) (nonnegative1191 p) (nonnegative53 p)
def d1193 (p : Pattern) : Int := if p 113 then d1192 p else d1190 p
theorem agree1193 (p q : Pattern) (h : Agree support p q) : d1193 p = d1193 q := by
  simp only [d1193, h 113 (by decide), agree1192 p q h, agree1190 p q h]
theorem nonnegative1193 (p : Pattern) : 0 ≤ d1193 p :=
  nonnegative_ite (p 113) (nonnegative1192 p) (nonnegative1190 p)
def d1194 (p : Pattern) : Int := if p 112 then d1193 p else d1188 p
theorem agree1194 (p q : Pattern) (h : Agree support p q) : d1194 p = d1194 q := by
  simp only [d1194, h 112 (by decide), agree1193 p q h, agree1188 p q h]
theorem nonnegative1194 (p : Pattern) : 0 ≤ d1194 p :=
  nonnegative_ite (p 112) (nonnegative1193 p) (nonnegative1188 p)
def d1195 (p : Pattern) : Int := if p 106 then d1194 p else d1183 p
theorem agree1195 (p q : Pattern) (h : Agree support p q) : d1195 p = d1195 q := by
  simp only [d1195, h 106 (by decide), agree1194 p q h, agree1183 p q h]
theorem nonnegative1195 (p : Pattern) : 0 ≤ d1195 p :=
  nonnegative_ite (p 106) (nonnegative1194 p) (nonnegative1183 p)
def d1196 (p : Pattern) : Int := if p 133 then d92 p else d86 p
theorem agree1196 (p q : Pattern) (h : Agree support p q) : d1196 p = d1196 q := by
  simp only [d1196, h 133 (by decide), agree92 p q h, agree86 p q h]
theorem nonnegative1196 (p : Pattern) : 0 ≤ d1196 p :=
  nonnegative_ite (p 133) (nonnegative92 p) (nonnegative86 p)
def d1197 (p : Pattern) : Int := if p 132 then d1196 p else d86 p
theorem agree1197 (p q : Pattern) (h : Agree support p q) : d1197 p = d1197 q := by
  simp only [d1197, h 132 (by decide), agree1196 p q h, agree86 p q h]
theorem nonnegative1197 (p : Pattern) : 0 ≤ d1197 p :=
  nonnegative_ite (p 132) (nonnegative1196 p) (nonnegative86 p)
def d1198 (p : Pattern) : Int := if p 113 then d1197 p else d1177 p
theorem agree1198 (p q : Pattern) (h : Agree support p q) : d1198 p = d1198 q := by
  simp only [d1198, h 113 (by decide), agree1197 p q h, agree1177 p q h]
theorem nonnegative1198 (p : Pattern) : 0 ≤ d1198 p :=
  nonnegative_ite (p 113) (nonnegative1197 p) (nonnegative1177 p)
def d1199 (p : Pattern) : Int := if p 133 then d69 p else d98 p
theorem agree1199 (p q : Pattern) (h : Agree support p q) : d1199 p = d1199 q := by
  simp only [d1199, h 133 (by decide), agree69 p q h, agree98 p q h]
theorem nonnegative1199 (p : Pattern) : 0 ≤ d1199 p :=
  nonnegative_ite (p 133) (nonnegative69 p) (nonnegative98 p)
end NetHack.Sokoban32Refined
