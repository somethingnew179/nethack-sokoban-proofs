/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1080 (p : Pattern) : d48 (change p 86 none) = d48 p := by
  change (if p 134 then d34 (change p 86 none) else d15 (change p 86 none)) = d48 p
  rw [sub1066, sub1047]
  rfl
theorem sub1081 (p : Pattern) : d49 (change p 86 none) = d49 p := by
  change (if p 134 then d25 (change p 86 none) else d41 (change p 86 none)) = d49 p
  rw [sub1057, sub1073]
  rfl
theorem sub1082 (p : Pattern) : d50 (change p 86 none) = d50 p := by
  change (if p 133 then d49 (change p 86 none) else d48 (change p 86 none)) = d50 p
  rw [sub1081, sub1080]
  rfl
theorem sub1083 (p : Pattern) : d51 (change p 86 none) = d51 p := by
  change (if p 132 then d50 (change p 86 none) else d47 (change p 86 none)) = d51 p
  rw [sub1082, sub1079]
  rfl
theorem sub1084 (p : Pattern) : d52 (change p 86 none) = d52 p := by
  change (if p 139 then d2 (change p 86 none) else d8 (change p 86 none)) = d52 p
  rw [sub1033, sub1039]
  rfl
theorem sub1085 (p : Pattern) : d53 (change p 86 none) = d53 p := by
  change (if p 138 then d52 (change p 86 none) else d15 (change p 86 none)) = d53 p
  rw [sub1084, sub1047]
  rfl
theorem sub1086 (p : Pattern) : d54 (change p 86 none) = d54 p := by
  change (if p 139 then d2 (change p 86 none) else d20 (change p 86 none)) = d54 p
  rw [sub1033, sub1052]
  rfl
theorem sub1087 (p : Pattern) : d55 (change p 86 none) = d55 p := by
  change (if p 138 then d54 (change p 86 none) else d25 (change p 86 none)) = d55 p
  rw [sub1086, sub1057]
  rfl
theorem sub1088 (p : Pattern) : d56 (change p 86 none) = d56 p := by
  change (if p 134 then d55 (change p 86 none) else d53 (change p 86 none)) = d56 p
  rw [sub1087, sub1085]
  rfl
theorem sub1089 (p : Pattern) : d57 (change p 86 none) = d57 p := by
  change (if p 133 then d56 (change p 86 none) else d53 (change p 86 none)) = d57 p
  rw [sub1088, sub1085]
  rfl
theorem sub1090 (p : Pattern) : d58 (change p 86 none) = d58 p := by
  change (if p 139 then d2 (change p 86 none) else d33 (change p 86 none)) = d58 p
  rw [sub1033, sub1065]
  rfl
theorem sub1091 (p : Pattern) : d59 (change p 86 none) = d59 p := by
  change (if p 138 then d58 (change p 86 none) else d34 (change p 86 none)) = d59 p
  rw [sub1090, sub1066]
  rfl
theorem sub1092 (p : Pattern) : d60 (change p 86 none) = d60 p := by
  change (if p 134 then d59 (change p 86 none) else d53 (change p 86 none)) = d60 p
  rw [sub1091, sub1085]
  rfl
theorem sub1093 (p : Pattern) : d61 (change p 86 none) = d61 p := by
  change (if p 139 then d2 (change p 86 none) else d38 (change p 86 none)) = d61 p
  rw [sub1033, sub1070]
  rfl
theorem sub1094 (p : Pattern) : d62 (change p 86 none) = d62 p := by
  change (if p 138 then d61 (change p 86 none) else d41 (change p 86 none)) = d62 p
  rw [sub1093, sub1073]
  rfl
theorem sub1095 (p : Pattern) : d63 (change p 86 none) = d63 p := by
  change (if p 134 then d55 (change p 86 none) else d62 (change p 86 none)) = d63 p
  rw [sub1087, sub1094]
  rfl
theorem sub1096 (p : Pattern) : d64 (change p 86 none) = d64 p := by
  change (if p 133 then d63 (change p 86 none) else d60 (change p 86 none)) = d64 p
  rw [sub1095, sub1092]
  rfl
theorem sub1097 (p : Pattern) : d65 (change p 86 none) = d65 p := by
  change (if p 132 then d64 (change p 86 none) else d57 (change p 86 none)) = d65 p
  rw [sub1096, sub1089]
  rfl
theorem sub1098 (p : Pattern) : d66 (change p 86 none) = d66 p := by
  change (if p 113 then d65 (change p 86 none) else d51 (change p 86 none)) = d66 p
  rw [sub1097, sub1083]
  rfl
theorem sub1099 (p : Pattern) : d67 (change p 86 none) = d67 p := by
  change (if p 112 then d66 (change p 86 none) else d45 (change p 86 none)) = d67 p
  rw [sub1098, sub1077]
  rfl
theorem sub1100 (p : Pattern) : d68 (change p 86 none) = d68 p := by
  change (if p 139 then d2 (change p 86 none) else d40 (change p 86 none)) = d68 p
  rw [sub1033, sub1072]
  rfl
theorem sub1101 (p : Pattern) : d69 (change p 86 none) = d69 p := by
  change (if p 138 then d68 (change p 86 none) else d40 (change p 86 none)) = d69 p
  rw [sub1100, sub1072]
  rfl
theorem sub1102 (p : Pattern) : d70 (change p 86 none) = d70 p := by
  change (if p 139 then d2 (change p 86 none) else d24 (change p 86 none)) = d70 p
  rw [sub1033, sub1056]
  rfl
theorem sub1103 (p : Pattern) : d71 (change p 86 none) = d71 p := by
  change (if p 138 then d70 (change p 86 none) else d24 (change p 86 none)) = d71 p
  rw [sub1102, sub1056]
  rfl
theorem sub1104 (p : Pattern) : d72 (change p 86 none) = d72 p := by
  change (if p 134 then d71 (change p 86 none) else d69 (change p 86 none)) = d72 p
  rw [sub1103, sub1101]
  rfl
theorem sub1105 (p : Pattern) : d73 (change p 86 none) = d73 p := by
  change (if p 133 then d72 (change p 86 none) else d27 (change p 86 none)) = d73 p
  rw [sub1104, sub1059]
  rfl
theorem sub1106 (p : Pattern) : d74 (change p 86 none) = d74 p := by
  change (if p 132 then d73 (change p 86 none) else d28 (change p 86 none)) = d74 p
  rw [sub1105, sub1060]
  rfl
theorem sub1107 (p : Pattern) : d75 (change p 86 none) = d75 p := by
  change (if p 134 then d70 (change p 86 none) else d68 (change p 86 none)) = d75 p
  rw [sub1102, sub1100]
  rfl
theorem sub1108 (p : Pattern) : d76 (change p 86 none) = d76 p := by
  change (if p 133 then d75 (change p 86 none) else d27 (change p 86 none)) = d76 p
  rw [sub1107, sub1059]
  rfl
theorem sub1109 (p : Pattern) : d77 (change p 86 none) = d77 p := by
  change (if p 132 then d76 (change p 86 none) else d28 (change p 86 none)) = d77 p
  rw [sub1108, sub1060]
  rfl
theorem sub1110 (p : Pattern) : d78 (change p 86 none) = d78 p := by
  change (if p 113 then d77 (change p 86 none) else d74 (change p 86 none)) = d78 p
  rw [sub1109, sub1106]
  rfl
theorem sub1111 (p : Pattern) : d79 (change p 86 none) = d79 p := by
  change (if p 133 then d75 (change p 86 none) else d46 (change p 86 none)) = d79 p
  rw [sub1107, sub1078]
  rfl
theorem sub1112 (p : Pattern) : d80 (change p 86 none) = d80 p := by
  change (if p 132 then d79 (change p 86 none) else d47 (change p 86 none)) = d80 p
  rw [sub1111, sub1079]
  rfl
theorem sub1113 (p : Pattern) : d81 (change p 86 none) = d81 p := by
  change (if p 133 then d75 (change p 86 none) else d56 (change p 86 none)) = d81 p
  rw [sub1107, sub1088]
  rfl
theorem sub1114 (p : Pattern) : d82 (change p 86 none) = d82 p := by
  change (if p 132 then d81 (change p 86 none) else d57 (change p 86 none)) = d82 p
  rw [sub1113, sub1089]
  rfl
theorem sub1115 (p : Pattern) : d83 (change p 86 none) = d83 p := by
  change (if p 113 then d82 (change p 86 none) else d80 (change p 86 none)) = d83 p
  rw [sub1114, sub1112]
  rfl
theorem sub1116 (p : Pattern) : d84 (change p 86 none) = d84 p := by
  change (if p 112 then d83 (change p 86 none) else d78 (change p 86 none)) = d84 p
  rw [sub1115, sub1110]
  rfl
theorem sub1117 (p : Pattern) : d85 (change p 86 none) = d85 p := by
  change (if p 106 then d84 (change p 86 none) else d67 (change p 86 none)) = d85 p
  rw [sub1116, sub1099]
  rfl
theorem sub1118 (p : Pattern) : d174 (change p 86 none) = d85 p := by
  change d85 (change p 86 none) = d85 p
  exact sub1117 p
theorem sub1119 (p : Pattern) : d117 (change p 86 none) = d117 p := by
  change (if p 112 then d83 (change p 86 none) else d77 (change p 86 none)) = d117 p
  rw [sub1115, sub1109]
  rfl
theorem sub1120 (p : Pattern) : d118 (change p 86 none) = d118 p := by
  change (if p 106 then d117 (change p 86 none) else d67 (change p 86 none)) = d118 p
  rw [sub1119, sub1099]
  rfl
theorem sub1121 (p : Pattern) : d175 (change p 86 none) = d118 p := by
  change d118 (change p 86 none) = d118 p
  exact sub1120 p
theorem sub1122 (p : Pattern) : d176 (change p 86 none) = d1071 p := by
  change (if p 80 then d175 (change p 86 none) else d174 (change p 86 none)) = d1071 p
  rw [sub1121, sub1118]
  rfl
theorem sub1123 (p : Pattern) : d0 (change p 113 none) = d0 p := by
  rfl
theorem sub1124 (p : Pattern) : d2 (change p 113 none) = d2 p := by
  rfl
theorem sub1125 (p : Pattern) : d3 (change p 113 none) = d3 p := by
  change (if p 161 then d2 (change p 113 none) else d0 (change p 113 none)) = d3 p
  rw [sub1124, sub1123]
  rfl
theorem sub1126 (p : Pattern) : d4 (change p 113 none) = d4 p := by
  change (if p 160 then d3 (change p 113 none) else d0 (change p 113 none)) = d4 p
  rw [sub1125, sub1123]
  rfl
theorem sub1127 (p : Pattern) : d5 (change p 113 none) = d5 p := by
  change (if p 160 then d2 (change p 113 none) else d0 (change p 113 none)) = d5 p
  rw [sub1124, sub1123]
  rfl
theorem sub1128 (p : Pattern) : d6 (change p 113 none) = d6 p := by
  change (if p 159 then d5 (change p 113 none) else d4 (change p 113 none)) = d6 p
  rw [sub1127, sub1126]
  rfl
theorem sub1129 (p : Pattern) : d7 (change p 113 none) = d7 p := by
  change (if p 159 then d2 (change p 113 none) else d4 (change p 113 none)) = d7 p
  rw [sub1124, sub1126]
  rfl
theorem sub1130 (p : Pattern) : d8 (change p 113 none) = d8 p := by
  change (if p 158 then d7 (change p 113 none) else d6 (change p 113 none)) = d8 p
  rw [sub1129, sub1128]
  rfl
theorem sub1131 (p : Pattern) : d1 (change p 113 none) = d1 p := by
  rfl
theorem sub1132 (p : Pattern) : d9 (change p 113 none) = d9 p := by
  change (if p 161 then d2 (change p 113 none) else d1 (change p 113 none)) = d9 p
  rw [sub1124, sub1131]
  rfl
theorem sub1133 (p : Pattern) : d10 (change p 113 none) = d10 p := by
  change (if p 160 then d9 (change p 113 none) else d1 (change p 113 none)) = d10 p
  rw [sub1132, sub1131]
  rfl
theorem sub1134 (p : Pattern) : d11 (change p 113 none) = d11 p := by
  change (if p 160 then d2 (change p 113 none) else d1 (change p 113 none)) = d11 p
  rw [sub1124, sub1131]
  rfl
theorem sub1135 (p : Pattern) : d12 (change p 113 none) = d12 p := by
  change (if p 159 then d11 (change p 113 none) else d10 (change p 113 none)) = d12 p
  rw [sub1134, sub1133]
  rfl
theorem sub1136 (p : Pattern) : d13 (change p 113 none) = d13 p := by
  change (if p 159 then d2 (change p 113 none) else d10 (change p 113 none)) = d13 p
  rw [sub1124, sub1133]
  rfl
theorem sub1137 (p : Pattern) : d14 (change p 113 none) = d14 p := by
  change (if p 158 then d13 (change p 113 none) else d12 (change p 113 none)) = d14 p
  rw [sub1136, sub1135]
  rfl
theorem sub1138 (p : Pattern) : d15 (change p 113 none) = d15 p := by
  change (if p 139 then d14 (change p 113 none) else d8 (change p 113 none)) = d15 p
  rw [sub1137, sub1130]
  rfl
theorem sub1139 (p : Pattern) : d16 (change p 113 none) = d16 p := by
  change (if p 138 then d15 (change p 113 none) else d8 (change p 113 none)) = d16 p
  rw [sub1138, sub1130]
  rfl
theorem sub1140 (p : Pattern) : d17 (change p 113 none) = d17 p := by
  change (if p 160 then d2 (change p 113 none) else d3 (change p 113 none)) = d17 p
  rw [sub1124, sub1125]
  rfl
theorem sub1141 (p : Pattern) : d18 (change p 113 none) = d18 p := by
  change (if p 159 then d17 (change p 113 none) else d4 (change p 113 none)) = d18 p
  rw [sub1140, sub1126]
  rfl
theorem sub1142 (p : Pattern) : d19 (change p 113 none) = d19 p := by
  change (if p 159 then d2 (change p 113 none) else d17 (change p 113 none)) = d19 p
  rw [sub1124, sub1140]
  rfl
theorem sub1143 (p : Pattern) : d20 (change p 113 none) = d20 p := by
  change (if p 158 then d19 (change p 113 none) else d18 (change p 113 none)) = d20 p
  rw [sub1142, sub1141]
  rfl
theorem sub1144 (p : Pattern) : d21 (change p 113 none) = d21 p := by
  change (if p 160 then d2 (change p 113 none) else d9 (change p 113 none)) = d21 p
  rw [sub1124, sub1132]
  rfl
theorem sub1145 (p : Pattern) : d22 (change p 113 none) = d22 p := by
  change (if p 159 then d21 (change p 113 none) else d10 (change p 113 none)) = d22 p
  rw [sub1144, sub1133]
  rfl
theorem sub1146 (p : Pattern) : d23 (change p 113 none) = d23 p := by
  change (if p 159 then d2 (change p 113 none) else d21 (change p 113 none)) = d23 p
  rw [sub1124, sub1144]
  rfl
theorem sub1147 (p : Pattern) : d24 (change p 113 none) = d24 p := by
  change (if p 158 then d23 (change p 113 none) else d22 (change p 113 none)) = d24 p
  rw [sub1146, sub1145]
  rfl
theorem sub1148 (p : Pattern) : d25 (change p 113 none) = d25 p := by
  change (if p 139 then d24 (change p 113 none) else d20 (change p 113 none)) = d25 p
  rw [sub1147, sub1143]
  rfl
theorem sub1149 (p : Pattern) : d26 (change p 113 none) = d26 p := by
  change (if p 138 then d25 (change p 113 none) else d20 (change p 113 none)) = d26 p
  rw [sub1148, sub1143]
  rfl
theorem sub1150 (p : Pattern) : d27 (change p 113 none) = d27 p := by
  change (if p 134 then d26 (change p 113 none) else d16 (change p 113 none)) = d27 p
  rw [sub1149, sub1139]
  rfl
theorem sub1151 (p : Pattern) : d28 (change p 113 none) = d28 p := by
  change (if p 133 then d27 (change p 113 none) else d16 (change p 113 none)) = d28 p
  rw [sub1150, sub1139]
  rfl
theorem sub1152 (p : Pattern) : d29 (change p 113 none) = d29 p := by
  change (if p 161 then d1 (change p 113 none) else d0 (change p 113 none)) = d29 p
  rw [sub1131, sub1123]
  rfl
theorem sub1153 (p : Pattern) : d30 (change p 113 none) = d30 p := by
  change (if p 160 then d2 (change p 113 none) else d29 (change p 113 none)) = d30 p
  rw [sub1124, sub1152]
  rfl
theorem sub1154 (p : Pattern) : d31 (change p 113 none) = d31 p := by
  change (if p 159 then d30 (change p 113 none) else d4 (change p 113 none)) = d31 p
  rw [sub1153, sub1126]
  rfl
theorem sub1155 (p : Pattern) : d32 (change p 113 none) = d32 p := by
  change (if p 159 then d2 (change p 113 none) else d30 (change p 113 none)) = d32 p
  rw [sub1124, sub1153]
  rfl
theorem sub1156 (p : Pattern) : d33 (change p 113 none) = d33 p := by
  change (if p 158 then d32 (change p 113 none) else d31 (change p 113 none)) = d33 p
  rw [sub1155, sub1154]
  rfl
theorem sub1157 (p : Pattern) : d34 (change p 113 none) = d34 p := by
  change (if p 139 then d24 (change p 113 none) else d33 (change p 113 none)) = d34 p
  rw [sub1147, sub1156]
  rfl
theorem sub1158 (p : Pattern) : d35 (change p 113 none) = d35 p := by
  change (if p 138 then d34 (change p 113 none) else d33 (change p 113 none)) = d35 p
  rw [sub1157, sub1156]
  rfl
theorem sub1159 (p : Pattern) : d36 (change p 113 none) = d36 p := by
  change (if p 134 then d35 (change p 113 none) else d16 (change p 113 none)) = d36 p
  rw [sub1158, sub1139]
  rfl
theorem sub1160 (p : Pattern) : d37 (change p 113 none) = d37 p := by
  change (if p 159 then d2 (change p 113 none) else d5 (change p 113 none)) = d37 p
  rw [sub1124, sub1127]
  rfl
theorem sub1161 (p : Pattern) : d38 (change p 113 none) = d38 p := by
  change (if p 158 then d37 (change p 113 none) else d6 (change p 113 none)) = d38 p
  rw [sub1160, sub1128]
  rfl
theorem sub1162 (p : Pattern) : d39 (change p 113 none) = d39 p := by
  change (if p 159 then d2 (change p 113 none) else d11 (change p 113 none)) = d39 p
  rw [sub1124, sub1134]
  rfl
theorem sub1163 (p : Pattern) : d40 (change p 113 none) = d40 p := by
  change (if p 158 then d39 (change p 113 none) else d12 (change p 113 none)) = d40 p
  rw [sub1162, sub1135]
  rfl
theorem sub1164 (p : Pattern) : d41 (change p 113 none) = d41 p := by
  change (if p 139 then d40 (change p 113 none) else d38 (change p 113 none)) = d41 p
  rw [sub1163, sub1161]
  rfl
theorem sub1165 (p : Pattern) : d42 (change p 113 none) = d42 p := by
  change (if p 138 then d41 (change p 113 none) else d38 (change p 113 none)) = d42 p
  rw [sub1164, sub1161]
  rfl
theorem sub1166 (p : Pattern) : d43 (change p 113 none) = d43 p := by
  change (if p 134 then d26 (change p 113 none) else d42 (change p 113 none)) = d43 p
  rw [sub1149, sub1165]
  rfl
theorem sub1167 (p : Pattern) : d44 (change p 113 none) = d44 p := by
  change (if p 133 then d43 (change p 113 none) else d36 (change p 113 none)) = d44 p
  rw [sub1166, sub1159]
  rfl
theorem sub1168 (p : Pattern) : d45 (change p 113 none) = d45 p := by
  change (if p 132 then d44 (change p 113 none) else d28 (change p 113 none)) = d45 p
  rw [sub1167, sub1151]
  rfl
theorem sub1169 (p : Pattern) : d228 (change p 113 none) = d45 p := by
  change d45 (change p 113 none) = d45 p
  exact sub1168 p
theorem sub1170 (p : Pattern) : d46 (change p 113 none) = d46 p := by
  change (if p 134 then d25 (change p 113 none) else d15 (change p 113 none)) = d46 p
  rw [sub1148, sub1138]
  rfl
theorem sub1171 (p : Pattern) : d47 (change p 113 none) = d47 p := by
  change (if p 133 then d46 (change p 113 none) else d15 (change p 113 none)) = d47 p
  rw [sub1170, sub1138]
  rfl
theorem sub1172 (p : Pattern) : d48 (change p 113 none) = d48 p := by
  change (if p 134 then d34 (change p 113 none) else d15 (change p 113 none)) = d48 p
  rw [sub1157, sub1138]
  rfl
theorem sub1173 (p : Pattern) : d49 (change p 113 none) = d49 p := by
  change (if p 134 then d25 (change p 113 none) else d41 (change p 113 none)) = d49 p
  rw [sub1148, sub1164]
  rfl
theorem sub1174 (p : Pattern) : d50 (change p 113 none) = d50 p := by
  change (if p 133 then d49 (change p 113 none) else d48 (change p 113 none)) = d50 p
  rw [sub1173, sub1172]
  rfl
theorem sub1175 (p : Pattern) : d51 (change p 113 none) = d51 p := by
  change (if p 132 then d50 (change p 113 none) else d47 (change p 113 none)) = d51 p
  rw [sub1174, sub1171]
  rfl
theorem sub1176 (p : Pattern) : d229 (change p 113 none) = d51 p := by
  change d51 (change p 113 none) = d51 p
  exact sub1175 p
theorem sub1177 (p : Pattern) : d230 (change p 113 none) = d1074 p := by
  change (if p 112 then d229 (change p 113 none) else d228 (change p 113 none)) = d1074 p
  rw [sub1176, sub1169]
  rfl
theorem sub1178 (p : Pattern) : d68 (change p 113 none) = d68 p := by
  change (if p 139 then d2 (change p 113 none) else d40 (change p 113 none)) = d68 p
  rw [sub1124, sub1163]
  rfl
theorem sub1179 (p : Pattern) : d69 (change p 113 none) = d69 p := by
  change (if p 138 then d68 (change p 113 none) else d40 (change p 113 none)) = d69 p
  rw [sub1178, sub1163]
  rfl
theorem sub1180 (p : Pattern) : d70 (change p 113 none) = d70 p := by
  change (if p 139 then d2 (change p 113 none) else d24 (change p 113 none)) = d70 p
  rw [sub1124, sub1147]
  rfl
theorem sub1181 (p : Pattern) : d71 (change p 113 none) = d71 p := by
  change (if p 138 then d70 (change p 113 none) else d24 (change p 113 none)) = d71 p
  rw [sub1180, sub1147]
  rfl
theorem sub1182 (p : Pattern) : d72 (change p 113 none) = d72 p := by
  change (if p 134 then d71 (change p 113 none) else d69 (change p 113 none)) = d72 p
  rw [sub1181, sub1179]
  rfl
theorem sub1183 (p : Pattern) : d73 (change p 113 none) = d73 p := by
  change (if p 133 then d72 (change p 113 none) else d27 (change p 113 none)) = d73 p
  rw [sub1182, sub1150]
  rfl
theorem sub1184 (p : Pattern) : d74 (change p 113 none) = d74 p := by
  change (if p 132 then d73 (change p 113 none) else d28 (change p 113 none)) = d74 p
  rw [sub1183, sub1151]
  rfl
theorem sub1185 (p : Pattern) : d231 (change p 113 none) = d74 p := by
  change d74 (change p 113 none) = d74 p
  exact sub1184 p
theorem sub1186 (p : Pattern) : d75 (change p 113 none) = d75 p := by
  change (if p 134 then d70 (change p 113 none) else d68 (change p 113 none)) = d75 p
  rw [sub1180, sub1178]
  rfl
theorem sub1187 (p : Pattern) : d79 (change p 113 none) = d79 p := by
  change (if p 133 then d75 (change p 113 none) else d46 (change p 113 none)) = d79 p
  rw [sub1186, sub1170]
  rfl
theorem sub1188 (p : Pattern) : d80 (change p 113 none) = d80 p := by
  change (if p 132 then d79 (change p 113 none) else d47 (change p 113 none)) = d80 p
  rw [sub1187, sub1171]
  rfl
theorem sub1189 (p : Pattern) : d232 (change p 113 none) = d80 p := by
  change d80 (change p 113 none) = d80 p
  exact sub1188 p
theorem sub1190 (p : Pattern) : d233 (change p 113 none) = d1075 p := by
  change (if p 112 then d232 (change p 113 none) else d231 (change p 113 none)) = d1075 p
  rw [sub1189, sub1185]
  rfl
theorem sub1191 (p : Pattern) : d234 (change p 113 none) = d1076 p := by
  change (if p 106 then d233 (change p 113 none) else d230 (change p 113 none)) = d1076 p
  rw [sub1190, sub1177]
  rfl
theorem sub1192 (p : Pattern) : d235 (change p 113 none) = d45 p := by
  change d45 (change p 113 none) = d45 p
  exact sub1168 p
theorem sub1193 (p : Pattern) : d97 (change p 113 none) = d97 p := by
  change (if p 139 then d2 (change p 113 none) else d14 (change p 113 none)) = d97 p
  rw [sub1124, sub1137]
  rfl
theorem sub1194 (p : Pattern) : d98 (change p 113 none) = d98 p := by
  change (if p 138 then d97 (change p 113 none) else d14 (change p 113 none)) = d98 p
  rw [sub1193, sub1137]
  rfl
theorem sub1195 (p : Pattern) : d99 (change p 113 none) = d99 p := by
  change (if p 134 then d71 (change p 113 none) else d98 (change p 113 none)) = d99 p
  rw [sub1181, sub1194]
  rfl
theorem sub1196 (p : Pattern) : d100 (change p 113 none) = d100 p := by
  change (if p 133 then d99 (change p 113 none) else d98 (change p 113 none)) = d100 p
  rw [sub1195, sub1194]
  rfl
theorem sub1197 (p : Pattern) : d101 (change p 113 none) = d101 p := by
  change (if p 133 then d72 (change p 113 none) else d99 (change p 113 none)) = d101 p
  rw [sub1182, sub1195]
  rfl
theorem sub1198 (p : Pattern) : d102 (change p 113 none) = d102 p := by
  change (if p 132 then d101 (change p 113 none) else d100 (change p 113 none)) = d102 p
  rw [sub1197, sub1196]
  rfl
theorem sub1199 (p : Pattern) : d236 (change p 113 none) = d102 p := by
  change d102 (change p 113 none) = d102 p
  exact sub1198 p
end NetHack.Sokoban32Refined
