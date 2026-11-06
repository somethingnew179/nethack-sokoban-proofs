/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1080 (p : Pattern) : d419 (change p 168 none) = d140 p := by
  change (if p 159 then d410 (change p 168 none) else d418 (change p 168 none)) = d140 p
  rw [sub1071, sub1079]
  rfl
theorem sub1081 (p : Pattern) : d420 (change p 168 none) = d188 p := by
  change (if p 158 then d386 (change p 168 none) else d419 (change p 168 none)) = d188 p
  rw [sub1046, sub1080]
  rfl
theorem sub1082 (p : Pattern) : d421 (change p 168 none) = d188 p := by
  change (if p 141 then d420 (change p 168 none) else d417 (change p 168 none)) = d188 p
  rw [sub1081, sub1078]
  simp only [ite_self]
theorem sub1083 (p : Pattern) : d422 (change p 168 none) = d189 p := by
  change (if p 134 then d402 (change p 168 none) else d421 (change p 168 none)) = d189 p
  rw [sub1062, sub1082]
  rfl
theorem sub1084 (p : Pattern) : d423 (change p 168 none) = d190 p := by
  change (if p 133 then d422 (change p 168 none) else d414 (change p 168 none)) = d190 p
  rw [sub1083, sub1075]
  rfl
theorem sub1085 (p : Pattern) : d424 (change p 168 none) = d191 p := by
  change (if p 158 then d380 (change p 168 none) else d407 (change p 168 none)) = d191 p
  rw [sub1038, sub1068]
  rfl
theorem sub1086 (p : Pattern) : d425 (change p 168 none) = d191 p := by
  change (if p 158 then d386 (change p 168 none) else d411 (change p 168 none)) = d191 p
  rw [sub1046, sub1072]
  rfl
theorem sub1087 (p : Pattern) : d426 (change p 168 none) = d191 p := by
  change (if p 141 then d425 (change p 168 none) else d424 (change p 168 none)) = d191 p
  rw [sub1086, sub1085]
  simp only [ite_self]
theorem sub1088 (p : Pattern) : d427 (change p 168 none) = d192 p := by
  change (if p 134 then d402 (change p 168 none) else d426 (change p 168 none)) = d192 p
  rw [sub1062, sub1087]
  rfl
theorem sub1089 (p : Pattern) : d428 (change p 168 none) = d193 p := by
  change (if p 133 then d402 (change p 168 none) else d427 (change p 168 none)) = d193 p
  rw [sub1062, sub1088]
  rfl
theorem sub1090 (p : Pattern) : d429 (change p 168 none) = d194 p := by
  change (if p 132 then d428 (change p 168 none) else d423 (change p 168 none)) = d194 p
  rw [sub1089, sub1084]
  rfl
theorem sub1091 (p : Pattern) : d430 (change p 168 none) = d195 p := by
  change (if p 108 then d429 (change p 168 none) else d404 (change p 168 none)) = d195 p
  rw [sub1090, sub1064]
  rfl
theorem sub1092 (p : Pattern) : d0 (change p 10000 (some 141)) = d0 p := by
  rfl
theorem sub1093 (p : Pattern) : d2 (change p 10000 (some 141)) = d2 p := by
  rfl
theorem sub1094 (p : Pattern) : d6 (change p 10000 (some 141)) = d6 p := by
  change (if p 193 then d2 (change p 10000 (some 141)) else d0 (change p 10000 (some 141))) = d6 p
  rw [sub1093, sub1092]
  rfl
theorem sub1095 (p : Pattern) : d7 (change p 10000 (some 141)) = d7 p := by
  change (if p 192 then d6 (change p 10000 (some 141)) else d0 (change p 10000 (some 141))) = d7 p
  rw [sub1094, sub1092]
  rfl
theorem sub1096 (p : Pattern) : d4 (change p 10000 (some 141)) = d4 p := by
  rfl
theorem sub1097 (p : Pattern) : d54 (change p 10000 (some 141)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 141)) else d2 (change p 10000 (some 141))) = d54 p
  rw [sub1096, sub1093]
  rfl
theorem sub1098 (p : Pattern) : d55 (change p 10000 (some 141)) = d55 p := by
  change (if p 192 then d54 (change p 10000 (some 141)) else d2 (change p 10000 (some 141))) = d55 p
  rw [sub1097, sub1093]
  rfl
theorem sub1099 (p : Pattern) : d56 (change p 10000 (some 141)) = d56 p := by
  change (if p 186 then d55 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d56 p
  rw [sub1098, sub1095]
  rfl
theorem sub1100 (p : Pattern) : d57 (change p 10000 (some 141)) = d57 p := by
  change (if p 160 then d56 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d57 p
  rw [sub1099, sub1095]
  rfl
theorem sub1101 (p : Pattern) : d106 (change p 10000 (some 141)) = d106 p := by
  change (if p 160 then d55 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d106 p
  rw [sub1098, sub1095]
  rfl
theorem sub1102 (p : Pattern) : d119 (change p 10000 (some 141)) = d119 p := by
  change (if p 187 then d55 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d119 p
  rw [sub1098, sub1095]
  rfl
theorem sub1103 (p : Pattern) : d120 (change p 10000 (some 141)) = d120 p := by
  change (if p 186 then d119 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d120 p
  rw [sub1102, sub1095]
  rfl
theorem sub1104 (p : Pattern) : d121 (change p 10000 (some 141)) = d121 p := by
  change (if p 160 then d55 (change p 10000 (some 141)) else d120 (change p 10000 (some 141))) = d121 p
  rw [sub1098, sub1103]
  rfl
theorem sub1105 (p : Pattern) : d122 (change p 10000 (some 141)) = d122 p := by
  change (if p 159 then d121 (change p 10000 (some 141)) else d106 (change p 10000 (some 141))) = d122 p
  rw [sub1104, sub1101]
  rfl
theorem sub1106 (p : Pattern) : d179 (change p 10000 (some 141)) = d179 p := by
  change (if p 158 then d122 (change p 10000 (some 141)) else d106 (change p 10000 (some 141))) = d179 p
  rw [sub1105, sub1101]
  rfl
theorem sub1107 (p : Pattern) : d180 (change p 10000 (some 141)) = d180 p := by
  change (if p 134 then d179 (change p 10000 (some 141)) else d57 (change p 10000 (some 141))) = d180 p
  rw [sub1106, sub1100]
  rfl
theorem sub1108 (p : Pattern) : d68 (change p 10000 (some 141)) = d68 p := by
  change (if p 158 then d55 (change p 10000 (some 141)) else d57 (change p 10000 (some 141))) = d68 p
  rw [sub1098, sub1100]
  rfl
theorem sub1109 (p : Pattern) : d181 (change p 10000 (some 141)) = d181 p := by
  change (if p 158 then d55 (change p 10000 (some 141)) else d122 (change p 10000 (some 141))) = d181 p
  rw [sub1098, sub1105]
  rfl
theorem sub1110 (p : Pattern) : d182 (change p 10000 (some 141)) = d182 p := by
  change (if p 134 then d181 (change p 10000 (some 141)) else d68 (change p 10000 (some 141))) = d182 p
  rw [sub1109, sub1108]
  rfl
theorem sub1111 (p : Pattern) : d183 (change p 10000 (some 141)) = d183 p := by
  change (if p 133 then d182 (change p 10000 (some 141)) else d180 (change p 10000 (some 141))) = d183 p
  rw [sub1110, sub1107]
  rfl
theorem sub1112 (p : Pattern) : d184 (change p 10000 (some 141)) = d184 p := by
  change (if p 133 then d55 (change p 10000 (some 141)) else d182 (change p 10000 (some 141))) = d184 p
  rw [sub1098, sub1110]
  rfl
theorem sub1113 (p : Pattern) : d185 (change p 10000 (some 141)) = d185 p := by
  change (if p 132 then d184 (change p 10000 (some 141)) else d183 (change p 10000 (some 141))) = d185 p
  rw [sub1112, sub1111]
  rfl
theorem sub1114 (p : Pattern) : d137 (change p 10000 (some 141)) = d137 p := by
  change (if p 186 then d55 (change p 10000 (some 141)) else d119 (change p 10000 (some 141))) = d137 p
  rw [sub1098, sub1102]
  rfl
theorem sub1115 (p : Pattern) : d139 (change p 10000 (some 141)) = d139 p := by
  change (if p 160 then d137 (change p 10000 (some 141)) else d120 (change p 10000 (some 141))) = d139 p
  rw [sub1114, sub1103]
  rfl
theorem sub1116 (p : Pattern) : d153 (change p 10000 (some 141)) = d153 p := by
  change (if p 159 then d139 (change p 10000 (some 141)) else d57 (change p 10000 (some 141))) = d153 p
  rw [sub1115, sub1100]
  rfl
theorem sub1117 (p : Pattern) : d186 (change p 10000 (some 141)) = d186 p := by
  change (if p 158 then d153 (change p 10000 (some 141)) else d57 (change p 10000 (some 141))) = d186 p
  rw [sub1116, sub1100]
  rfl
theorem sub1118 (p : Pattern) : d187 (change p 10000 (some 141)) = d187 p := by
  change (if p 134 then d55 (change p 10000 (some 141)) else d186 (change p 10000 (some 141))) = d187 p
  rw [sub1098, sub1117]
  rfl
theorem sub1119 (p : Pattern) : d138 (change p 10000 (some 141)) = d138 p := by
  change (if p 160 then d137 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d138 p
  rw [sub1114, sub1095]
  rfl
theorem sub1120 (p : Pattern) : d140 (change p 10000 (some 141)) = d140 p := by
  change (if p 159 then d139 (change p 10000 (some 141)) else d138 (change p 10000 (some 141))) = d140 p
  rw [sub1115, sub1119]
  rfl
theorem sub1121 (p : Pattern) : d188 (change p 10000 (some 141)) = d188 p := by
  change (if p 158 then d55 (change p 10000 (some 141)) else d140 (change p 10000 (some 141))) = d188 p
  rw [sub1098, sub1120]
  rfl
theorem sub1122 (p : Pattern) : d189 (change p 10000 (some 141)) = d189 p := by
  change (if p 134 then d55 (change p 10000 (some 141)) else d188 (change p 10000 (some 141))) = d189 p
  rw [sub1098, sub1121]
  rfl
theorem sub1123 (p : Pattern) : d190 (change p 10000 (some 141)) = d190 p := by
  change (if p 133 then d189 (change p 10000 (some 141)) else d187 (change p 10000 (some 141))) = d190 p
  rw [sub1122, sub1118]
  rfl
theorem sub1124 (p : Pattern) : d191 (change p 10000 (some 141)) = d191 p := by
  change (if p 158 then d55 (change p 10000 (some 141)) else d153 (change p 10000 (some 141))) = d191 p
  rw [sub1098, sub1116]
  rfl
theorem sub1125 (p : Pattern) : d192 (change p 10000 (some 141)) = d192 p := by
  change (if p 134 then d55 (change p 10000 (some 141)) else d191 (change p 10000 (some 141))) = d192 p
  rw [sub1098, sub1124]
  rfl
theorem sub1126 (p : Pattern) : d193 (change p 10000 (some 141)) = d193 p := by
  change (if p 133 then d55 (change p 10000 (some 141)) else d192 (change p 10000 (some 141))) = d193 p
  rw [sub1098, sub1125]
  rfl
theorem sub1127 (p : Pattern) : d194 (change p 10000 (some 141)) = d194 p := by
  change (if p 132 then d193 (change p 10000 (some 141)) else d190 (change p 10000 (some 141))) = d194 p
  rw [sub1126, sub1123]
  rfl
theorem sub1128 (p : Pattern) : d195 (change p 10000 (some 141)) = d195 p := by
  change (if p 108 then d194 (change p 10000 (some 141)) else d185 (change p 10000 (some 141))) = d195 p
  rw [sub1127, sub1113]
  rfl
theorem sub1129 (p : Pattern) : d0 (change p 158 (some 159)) = d0 p := by
  rfl
theorem sub1130 (p : Pattern) : d2 (change p 158 (some 159)) = d2 p := by
  rfl
theorem sub1131 (p : Pattern) : d6 (change p 158 (some 159)) = d6 p := by
  change (if p 193 then d2 (change p 158 (some 159)) else d0 (change p 158 (some 159))) = d6 p
  rw [sub1130, sub1129]
  rfl
theorem sub1132 (p : Pattern) : d7 (change p 158 (some 159)) = d7 p := by
  change (if p 192 then d6 (change p 158 (some 159)) else d0 (change p 158 (some 159))) = d7 p
  rw [sub1131, sub1129]
  rfl
theorem sub1133 (p : Pattern) : d4 (change p 158 (some 159)) = d4 p := by
  rfl
theorem sub1134 (p : Pattern) : d54 (change p 158 (some 159)) = d54 p := by
  change (if p 193 then d4 (change p 158 (some 159)) else d2 (change p 158 (some 159))) = d54 p
  rw [sub1133, sub1130]
  rfl
theorem sub1135 (p : Pattern) : d55 (change p 158 (some 159)) = d55 p := by
  change (if p 192 then d54 (change p 158 (some 159)) else d2 (change p 158 (some 159))) = d55 p
  rw [sub1134, sub1130]
  rfl
theorem sub1136 (p : Pattern) : d56 (change p 158 (some 159)) = d56 p := by
  change (if p 186 then d55 (change p 158 (some 159)) else d7 (change p 158 (some 159))) = d56 p
  rw [sub1135, sub1132]
  rfl
theorem sub1137 (p : Pattern) : d57 (change p 158 (some 159)) = d57 p := by
  change (if p 160 then d56 (change p 158 (some 159)) else d7 (change p 158 (some 159))) = d57 p
  rw [sub1136, sub1132]
  rfl
theorem sub1138 (p : Pattern) : d68 (change p 158 (some 159)) = d57 p := by
  change d57 (change p 158 (some 159)) = d57 p
  exact sub1137 p
theorem sub1139 (p : Pattern) : d1 (change p 158 (some 159)) = d1 p := by
  rfl
theorem sub1140 (p : Pattern) : d8 (change p 158 (some 159)) = d8 p := by
  change (if p 271 then d1 (change p 158 (some 159)) else d0 (change p 158 (some 159))) = d8 p
  rw [sub1139, sub1129]
  rfl
theorem sub1141 (p : Pattern) : d3 (change p 158 (some 159)) = d3 p := by
  rfl
theorem sub1142 (p : Pattern) : d9 (change p 158 (some 159)) = d9 p := by
  change (if p 271 then d3 (change p 158 (some 159)) else d2 (change p 158 (some 159))) = d9 p
  rw [sub1141, sub1130]
  rfl
theorem sub1143 (p : Pattern) : d10 (change p 158 (some 159)) = d10 p := by
  change (if p 193 then d9 (change p 158 (some 159)) else d8 (change p 158 (some 159))) = d10 p
  rw [sub1142, sub1140]
  rfl
theorem sub1144 (p : Pattern) : d11 (change p 158 (some 159)) = d11 p := by
  change (if p 192 then d10 (change p 158 (some 159)) else d8 (change p 158 (some 159))) = d11 p
  rw [sub1143, sub1140]
  rfl
theorem sub1145 (p : Pattern) : d12 (change p 158 (some 159)) = d12 p := by
  change (if p 168 then d11 (change p 158 (some 159)) else d7 (change p 158 (some 159))) = d12 p
  rw [sub1144, sub1132]
  rfl
theorem sub1146 (p : Pattern) : d5 (change p 158 (some 159)) = d5 p := by
  rfl
theorem sub1147 (p : Pattern) : d58 (change p 158 (some 159)) = d58 p := by
  change (if p 271 then d5 (change p 158 (some 159)) else d4 (change p 158 (some 159))) = d58 p
  rw [sub1146, sub1133]
  rfl
theorem sub1148 (p : Pattern) : d59 (change p 158 (some 159)) = d59 p := by
  change (if p 193 then d58 (change p 158 (some 159)) else d9 (change p 158 (some 159))) = d59 p
  rw [sub1147, sub1142]
  rfl
theorem sub1149 (p : Pattern) : d60 (change p 158 (some 159)) = d60 p := by
  change (if p 192 then d59 (change p 158 (some 159)) else d9 (change p 158 (some 159))) = d60 p
  rw [sub1148, sub1142]
  rfl
theorem sub1150 (p : Pattern) : d61 (change p 158 (some 159)) = d61 p := by
  change (if p 186 then d60 (change p 158 (some 159)) else d11 (change p 158 (some 159))) = d61 p
  rw [sub1149, sub1144]
  rfl
theorem sub1151 (p : Pattern) : d62 (change p 158 (some 159)) = d62 p := by
  change (if p 168 then d61 (change p 158 (some 159)) else d56 (change p 158 (some 159))) = d62 p
  rw [sub1150, sub1136]
  rfl
theorem sub1152 (p : Pattern) : d63 (change p 158 (some 159)) = d63 p := by
  change (if p 160 then d62 (change p 158 (some 159)) else d12 (change p 158 (some 159))) = d63 p
  rw [sub1151, sub1145]
  rfl
theorem sub1153 (p : Pattern) : d69 (change p 158 (some 159)) = d63 p := by
  change d63 (change p 158 (some 159)) = d63 p
  exact sub1152 p
theorem sub1154 (p : Pattern) : d70 (change p 158 (some 159)) = d64 p := by
  change (if p 141 then d69 (change p 158 (some 159)) else d68 (change p 158 (some 159))) = d64 p
  rw [sub1153, sub1138]
  rfl
theorem sub1155 (p : Pattern) : d106 (change p 158 (some 159)) = d106 p := by
  change (if p 160 then d55 (change p 158 (some 159)) else d7 (change p 158 (some 159))) = d106 p
  rw [sub1135, sub1132]
  rfl
theorem sub1156 (p : Pattern) : d229 (change p 158 (some 159)) = d106 p := by
  change d106 (change p 158 (some 159)) = d106 p
  exact sub1155 p
theorem sub1157 (p : Pattern) : d65 (change p 158 (some 159)) = d65 p := by
  change (if p 168 then d60 (change p 158 (some 159)) else d55 (change p 158 (some 159))) = d65 p
  rw [sub1149, sub1135]
  rfl
theorem sub1158 (p : Pattern) : d109 (change p 158 (some 159)) = d109 p := by
  change (if p 160 then d65 (change p 158 (some 159)) else d12 (change p 158 (some 159))) = d109 p
  rw [sub1157, sub1145]
  rfl
theorem sub1159 (p : Pattern) : d230 (change p 158 (some 159)) = d109 p := by
  change d109 (change p 158 (some 159)) = d109 p
  exact sub1158 p
theorem sub1160 (p : Pattern) : d231 (change p 158 (some 159)) = d227 p := by
  change (if p 141 then d230 (change p 158 (some 159)) else d229 (change p 158 (some 159))) = d227 p
  rw [sub1159, sub1156]
  rfl
theorem sub1161 (p : Pattern) : d232 (change p 158 (some 159)) = d228 p := by
  change (if p 134 then d231 (change p 158 (some 159)) else d70 (change p 158 (some 159))) = d228 p
  rw [sub1160, sub1154]
  rfl
theorem sub1162 (p : Pattern) : d119 (change p 158 (some 159)) = d119 p := by
  change (if p 187 then d55 (change p 158 (some 159)) else d7 (change p 158 (some 159))) = d119 p
  rw [sub1135, sub1132]
  rfl
theorem sub1163 (p : Pattern) : d120 (change p 158 (some 159)) = d120 p := by
  change (if p 186 then d119 (change p 158 (some 159)) else d7 (change p 158 (some 159))) = d120 p
  rw [sub1162, sub1132]
  rfl
theorem sub1164 (p : Pattern) : d121 (change p 158 (some 159)) = d121 p := by
  change (if p 160 then d55 (change p 158 (some 159)) else d120 (change p 158 (some 159))) = d121 p
  rw [sub1135, sub1163]
  rfl
theorem sub1165 (p : Pattern) : d122 (change p 158 (some 159)) = d121 p := by
  change d121 (change p 158 (some 159)) = d121 p
  exact sub1164 p
theorem sub1166 (p : Pattern) : d181 (change p 158 (some 159)) = d121 p := by
  change d122 (change p 158 (some 159)) = d121 p
  exact sub1165 p
theorem sub1167 (p : Pattern) : d125 (change p 158 (some 159)) = d125 p := by
  change (if p 187 then d60 (change p 158 (some 159)) else d11 (change p 158 (some 159))) = d125 p
  rw [sub1149, sub1144]
  rfl
theorem sub1168 (p : Pattern) : d126 (change p 158 (some 159)) = d126 p := by
  change (if p 186 then d125 (change p 158 (some 159)) else d11 (change p 158 (some 159))) = d126 p
  rw [sub1167, sub1144]
  rfl
theorem sub1169 (p : Pattern) : d127 (change p 158 (some 159)) = d127 p := by
  change (if p 168 then d126 (change p 158 (some 159)) else d120 (change p 158 (some 159))) = d127 p
  rw [sub1168, sub1163]
  rfl
theorem sub1170 (p : Pattern) : d128 (change p 158 (some 159)) = d128 p := by
  change (if p 160 then d65 (change p 158 (some 159)) else d127 (change p 158 (some 159))) = d128 p
  rw [sub1157, sub1169]
  rfl
theorem sub1171 (p : Pattern) : d129 (change p 158 (some 159)) = d128 p := by
  change d128 (change p 158 (some 159)) = d128 p
  exact sub1170 p
theorem sub1172 (p : Pattern) : d240 (change p 158 (some 159)) = d128 p := by
  change d129 (change p 158 (some 159)) = d128 p
  exact sub1171 p
theorem sub1173 (p : Pattern) : d241 (change p 158 (some 159)) = d988 p := by
  change (if p 141 then d240 (change p 158 (some 159)) else d181 (change p 158 (some 159))) = d988 p
  rw [sub1172, sub1166]
  rfl
theorem sub1174 (p : Pattern) : d242 (change p 158 (some 159)) = d989 p := by
  change (if p 134 then d241 (change p 158 (some 159)) else d70 (change p 158 (some 159))) = d989 p
  rw [sub1173, sub1154]
  rfl
theorem sub1175 (p : Pattern) : d315 (change p 158 (some 159)) = d990 p := by
  change (if p 133 then d242 (change p 158 (some 159)) else d232 (change p 158 (some 159))) = d990 p
  rw [sub1174, sub1161]
  rfl
theorem sub1176 (p : Pattern) : d66 (change p 158 (some 159)) = d66 p := by
  change (if p 141 then d65 (change p 158 (some 159)) else d55 (change p 158 (some 159))) = d66 p
  rw [sub1157, sub1135]
  rfl
theorem sub1177 (p : Pattern) : d244 (change p 158 (some 159)) = d991 p := by
  change (if p 133 then d66 (change p 158 (some 159)) else d242 (change p 158 (some 159))) = d991 p
  rw [sub1176, sub1174]
  rfl
theorem sub1178 (p : Pattern) : d316 (change p 158 (some 159)) = d992 p := by
  change (if p 132 then d244 (change p 158 (some 159)) else d315 (change p 158 (some 159))) = d992 p
  rw [sub1177, sub1175]
  rfl
theorem sub1179 (p : Pattern) : d71 (change p 158 (some 159)) = d67 p := by
  change (if p 134 then d66 (change p 158 (some 159)) else d70 (change p 158 (some 159))) = d67 p
  rw [sub1176, sub1154]
  rfl
theorem sub1180 (p : Pattern) : d137 (change p 158 (some 159)) = d137 p := by
  change (if p 186 then d55 (change p 158 (some 159)) else d119 (change p 158 (some 159))) = d137 p
  rw [sub1135, sub1162]
  rfl
theorem sub1181 (p : Pattern) : d139 (change p 158 (some 159)) = d139 p := by
  change (if p 160 then d137 (change p 158 (some 159)) else d120 (change p 158 (some 159))) = d139 p
  rw [sub1180, sub1163]
  rfl
theorem sub1182 (p : Pattern) : d140 (change p 158 (some 159)) = d139 p := by
  change d139 (change p 158 (some 159)) = d139 p
  exact sub1181 p
theorem sub1183 (p : Pattern) : d188 (change p 158 (some 159)) = d139 p := by
  change d140 (change p 158 (some 159)) = d139 p
  exact sub1182 p
theorem sub1184 (p : Pattern) : d143 (change p 158 (some 159)) = d143 p := by
  change (if p 186 then d60 (change p 158 (some 159)) else d125 (change p 158 (some 159))) = d143 p
  rw [sub1149, sub1167]
  rfl
theorem sub1185 (p : Pattern) : d144 (change p 158 (some 159)) = d144 p := by
  change (if p 168 then d143 (change p 158 (some 159)) else d137 (change p 158 (some 159))) = d144 p
  rw [sub1184, sub1180]
  rfl
theorem sub1186 (p : Pattern) : d146 (change p 158 (some 159)) = d146 p := by
  change (if p 160 then d144 (change p 158 (some 159)) else d127 (change p 158 (some 159))) = d146 p
  rw [sub1185, sub1169]
  rfl
theorem sub1187 (p : Pattern) : d147 (change p 158 (some 159)) = d146 p := by
  change d146 (change p 158 (some 159)) = d146 p
  exact sub1186 p
theorem sub1188 (p : Pattern) : d249 (change p 158 (some 159)) = d146 p := by
  change d147 (change p 158 (some 159)) = d146 p
  exact sub1187 p
theorem sub1189 (p : Pattern) : d250 (change p 158 (some 159)) = d993 p := by
  change (if p 141 then d249 (change p 158 (some 159)) else d188 (change p 158 (some 159))) = d993 p
  rw [sub1188, sub1183]
  rfl
theorem sub1190 (p : Pattern) : d251 (change p 158 (some 159)) = d994 p := by
  change (if p 134 then d66 (change p 158 (some 159)) else d250 (change p 158 (some 159))) = d994 p
  rw [sub1176, sub1189]
  rfl
theorem sub1191 (p : Pattern) : d317 (change p 158 (some 159)) = d995 p := by
  change (if p 133 then d251 (change p 158 (some 159)) else d71 (change p 158 (some 159))) = d995 p
  rw [sub1190, sub1179]
  rfl
theorem sub1192 (p : Pattern) : d153 (change p 158 (some 159)) = d139 p := by
  change d139 (change p 158 (some 159)) = d139 p
  exact sub1181 p
theorem sub1193 (p : Pattern) : d191 (change p 158 (some 159)) = d139 p := by
  change d153 (change p 158 (some 159)) = d139 p
  exact sub1192 p
theorem sub1194 (p : Pattern) : d155 (change p 158 (some 159)) = d146 p := by
  change d146 (change p 158 (some 159)) = d146 p
  exact sub1186 p
theorem sub1195 (p : Pattern) : d253 (change p 158 (some 159)) = d146 p := by
  change d155 (change p 158 (some 159)) = d146 p
  exact sub1194 p
theorem sub1196 (p : Pattern) : d254 (change p 158 (some 159)) = d993 p := by
  change (if p 141 then d253 (change p 158 (some 159)) else d191 (change p 158 (some 159))) = d993 p
  rw [sub1195, sub1193]
  rfl
theorem sub1197 (p : Pattern) : d255 (change p 158 (some 159)) = d994 p := by
  change (if p 134 then d66 (change p 158 (some 159)) else d254 (change p 158 (some 159))) = d994 p
  rw [sub1176, sub1196]
  rfl
theorem sub1198 (p : Pattern) : d256 (change p 158 (some 159)) = d996 p := by
  change (if p 133 then d66 (change p 158 (some 159)) else d255 (change p 158 (some 159))) = d996 p
  rw [sub1176, sub1197]
  rfl
theorem sub1199 (p : Pattern) : d318 (change p 158 (some 159)) = d997 p := by
  change (if p 132 then d256 (change p 158 (some 159)) else d317 (change p 158 (some 159))) = d997 p
  rw [sub1198, sub1191]
  rfl
end NetHack.Sokoban12CostPartition
