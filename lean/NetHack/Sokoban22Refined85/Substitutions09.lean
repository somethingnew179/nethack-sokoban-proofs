/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1080 (p : Pattern) : d54 (change p 48 none) = d54 p := by
  change (if p 163 then d53 (change p 48 none) else d16 (change p 48 none)) = d54 p
  rw [sub1079, sub1037]
  rfl
theorem sub1081 (p : Pattern) : d55 (change p 48 none) = d55 p := by
  change (if p 163 then d26 (change p 48 none) else d20 (change p 48 none)) = d55 p
  rw [sub1049, sub1042]
  rfl
theorem sub1082 (p : Pattern) : d56 (change p 48 none) = d56 p := by
  change (if p 162 then d55 (change p 48 none) else d54 (change p 48 none)) = d56 p
  rw [sub1081, sub1080]
  rfl
theorem sub1083 (p : Pattern) : d10 (change p 48 none) = d10 p := by
  rfl
theorem sub1084 (p : Pattern) : d57 (change p 48 none) = d57 p := by
  change (if p 247 then d12 (change p 48 none) else d10 (change p 48 none)) = d57 p
  rw [sub1033, sub1083]
  rfl
theorem sub1085 (p : Pattern) : d58 (change p 48 none) = d58 p := by
  change (if p 246 then d57 (change p 48 none) else d10 (change p 48 none)) = d58 p
  rw [sub1084, sub1083]
  rfl
theorem sub1086 (p : Pattern) : d59 (change p 48 none) = d59 p := by
  change (if p 204 then d12 (change p 48 none) else d58 (change p 48 none)) = d59 p
  rw [sub1033, sub1085]
  rfl
theorem sub1087 (p : Pattern) : d60 (change p 48 none) = d60 p := by
  change (if p 182 then d59 (change p 48 none) else d58 (change p 48 none)) = d60 p
  rw [sub1086, sub1085]
  rfl
theorem sub1088 (p : Pattern) : d61 (change p 48 none) = d61 p := by
  change (if p 163 then d60 (change p 48 none) else d20 (change p 48 none)) = d61 p
  rw [sub1087, sub1042]
  rfl
theorem sub1089 (p : Pattern) : d62 (change p 48 none) = d62 p := by
  change (if p 182 then d41 (change p 48 none) else d40 (change p 48 none)) = d62 p
  rw [sub1067, sub1066]
  rfl
theorem sub1090 (p : Pattern) : d63 (change p 48 none) = d63 p := by
  change (if p 163 then d12 (change p 48 none) else d62 (change p 48 none)) = d63 p
  rw [sub1033, sub1089]
  rfl
theorem sub1091 (p : Pattern) : d64 (change p 48 none) = d64 p := by
  change (if p 162 then d63 (change p 48 none) else d61 (change p 48 none)) = d64 p
  rw [sub1090, sub1088]
  rfl
theorem sub1092 (p : Pattern) : d65 (change p 48 none) = d65 p := by
  change (if p 161 then d64 (change p 48 none) else d56 (change p 48 none)) = d65 p
  rw [sub1091, sub1082]
  rfl
theorem sub1093 (p : Pattern) : d66 (change p 48 none) = d66 p := by
  change (if p 182 then d12 (change p 48 none) else d31 (change p 48 none)) = d66 p
  rw [sub1033, sub1055]
  rfl
theorem sub1094 (p : Pattern) : d67 (change p 48 none) = d67 p := by
  change (if p 163 then d66 (change p 48 none) else d37 (change p 48 none)) = d67 p
  rw [sub1093, sub1062]
  rfl
theorem sub1095 (p : Pattern) : d68 (change p 48 none) = d68 p := by
  change (if p 163 then d48 (change p 48 none) else d43 (change p 48 none)) = d68 p
  rw [sub1074, sub1069]
  rfl
theorem sub1096 (p : Pattern) : d69 (change p 48 none) = d69 p := by
  change (if p 162 then d68 (change p 48 none) else d67 (change p 48 none)) = d69 p
  rw [sub1095, sub1094]
  rfl
theorem sub1097 (p : Pattern) : d70 (change p 48 none) = d70 p := by
  change (if p 182 then d12 (change p 48 none) else d58 (change p 48 none)) = d70 p
  rw [sub1033, sub1085]
  rfl
theorem sub1098 (p : Pattern) : d71 (change p 48 none) = d71 p := by
  change (if p 163 then d70 (change p 48 none) else d43 (change p 48 none)) = d71 p
  rw [sub1097, sub1069]
  rfl
theorem sub1099 (p : Pattern) : d72 (change p 48 none) = d72 p := by
  change (if p 182 then d12 (change p 48 none) else d40 (change p 48 none)) = d72 p
  rw [sub1033, sub1066]
  rfl
theorem sub1100 (p : Pattern) : d73 (change p 48 none) = d73 p := by
  change (if p 163 then d12 (change p 48 none) else d72 (change p 48 none)) = d73 p
  rw [sub1033, sub1099]
  rfl
theorem sub1101 (p : Pattern) : d74 (change p 48 none) = d74 p := by
  change (if p 162 then d73 (change p 48 none) else d71 (change p 48 none)) = d74 p
  rw [sub1100, sub1098]
  rfl
theorem sub1102 (p : Pattern) : d75 (change p 48 none) = d75 p := by
  change (if p 161 then d74 (change p 48 none) else d69 (change p 48 none)) = d75 p
  rw [sub1101, sub1096]
  rfl
theorem sub1103 (p : Pattern) : d76 (change p 48 none) = d76 p := by
  change (if p 160 then d75 (change p 48 none) else d65 (change p 48 none)) = d76 p
  rw [sub1102, sub1092]
  rfl
theorem sub1104 (p : Pattern) : d77 (change p 48 none) = d77 p := by
  change (if p 141 then d76 (change p 48 none) else d52 (change p 48 none)) = d77 p
  rw [sub1103, sub1078]
  rfl
theorem sub1105 (p : Pattern) : d78 (change p 48 none) = d78 p := by
  change (if p 182 then d36 (change p 48 none) else d35 (change p 48 none)) = d78 p
  rw [sub1061, sub1060]
  rfl
theorem sub1106 (p : Pattern) : d79 (change p 48 none) = d79 p := by
  change (if p 163 then d78 (change p 48 none) else d53 (change p 48 none)) = d79 p
  rw [sub1105, sub1079]
  rfl
theorem sub1107 (p : Pattern) : d80 (change p 48 none) = d80 p := by
  change (if p 162 then d63 (change p 48 none) else d79 (change p 48 none)) = d80 p
  rw [sub1090, sub1106]
  rfl
theorem sub1108 (p : Pattern) : d81 (change p 48 none) = d81 p := by
  change (if p 161 then d12 (change p 48 none) else d80 (change p 48 none)) = d81 p
  rw [sub1033, sub1107]
  rfl
theorem sub1109 (p : Pattern) : d82 (change p 48 none) = d82 p := by
  change (if p 160 then d81 (change p 48 none) else d29 (change p 48 none)) = d82 p
  rw [sub1108, sub1052]
  rfl
theorem sub1110 (p : Pattern) : d83 (change p 48 none) = d83 p := by
  change (if p 163 then d12 (change p 48 none) else d78 (change p 48 none)) = d83 p
  rw [sub1033, sub1105]
  rfl
theorem sub1111 (p : Pattern) : d84 (change p 48 none) = d84 p := by
  change (if p 162 then d12 (change p 48 none) else d83 (change p 48 none)) = d84 p
  rw [sub1033, sub1110]
  rfl
theorem sub1112 (p : Pattern) : d85 (change p 48 none) = d85 p := by
  change (if p 161 then d12 (change p 48 none) else d84 (change p 48 none)) = d85 p
  rw [sub1033, sub1111]
  rfl
theorem sub1113 (p : Pattern) : d86 (change p 48 none) = d86 p := by
  change (if p 160 then d85 (change p 48 none) else d65 (change p 48 none)) = d86 p
  rw [sub1112, sub1092]
  rfl
theorem sub1114 (p : Pattern) : d87 (change p 48 none) = d87 p := by
  change (if p 141 then d86 (change p 48 none) else d82 (change p 48 none)) = d87 p
  rw [sub1113, sub1109]
  rfl
theorem sub1115 (p : Pattern) : d88 (change p 48 none) = d88 p := by
  change (if p 138 then d87 (change p 48 none) else d77 (change p 48 none)) = d88 p
  rw [sub1114, sub1104]
  rfl
theorem sub1116 (p : Pattern) : d89 (change p 48 none) = d89 p := by
  change (if p 163 then d62 (change p 48 none) else d26 (change p 48 none)) = d89 p
  rw [sub1089, sub1049]
  rfl
theorem sub1117 (p : Pattern) : d90 (change p 48 none) = d90 p := by
  change (if p 162 then d63 (change p 48 none) else d89 (change p 48 none)) = d90 p
  rw [sub1090, sub1116]
  rfl
theorem sub1118 (p : Pattern) : d91 (change p 48 none) = d91 p := by
  change (if p 162 then d12 (change p 48 none) else d63 (change p 48 none)) = d91 p
  rw [sub1033, sub1090]
  rfl
theorem sub1119 (p : Pattern) : d92 (change p 48 none) = d92 p := by
  change (if p 161 then d91 (change p 48 none) else d90 (change p 48 none)) = d92 p
  rw [sub1118, sub1117]
  rfl
theorem sub1120 (p : Pattern) : d93 (change p 48 none) = d93 p := by
  change (if p 161 then d12 (change p 48 none) else d91 (change p 48 none)) = d93 p
  rw [sub1033, sub1118]
  rfl
theorem sub1121 (p : Pattern) : d94 (change p 48 none) = d94 p := by
  change (if p 160 then d93 (change p 48 none) else d92 (change p 48 none)) = d94 p
  rw [sub1120, sub1119]
  rfl
theorem sub1122 (p : Pattern) : d95 (change p 48 none) = d95 p := by
  change (if p 160 then d12 (change p 48 none) else d93 (change p 48 none)) = d95 p
  rw [sub1033, sub1120]
  rfl
theorem sub1123 (p : Pattern) : d96 (change p 48 none) = d96 p := by
  change (if p 141 then d95 (change p 48 none) else d94 (change p 48 none)) = d96 p
  rw [sub1122, sub1121]
  rfl
theorem sub1124 (p : Pattern) : d97 (change p 48 none) = d97 p := by
  change (if p 138 then d96 (change p 48 none) else d87 (change p 48 none)) = d97 p
  rw [sub1123, sub1114]
  rfl
theorem sub1125 (p : Pattern) : d98 (change p 48 none) = d98 p := by
  change (if p 116 then d97 (change p 48 none) else d88 (change p 48 none)) = d98 p
  rw [sub1124, sub1115]
  rfl
theorem sub1126 (p : Pattern) : d99 (change p 48 none) = d99 p := by
  change (if p 138 then d12 (change p 48 none) else d87 (change p 48 none)) = d99 p
  rw [sub1033, sub1114]
  rfl
theorem sub1127 (p : Pattern) : d100 (change p 48 none) = d100 p := by
  change (if p 116 then d99 (change p 48 none) else d88 (change p 48 none)) = d100 p
  rw [sub1126, sub1115]
  rfl
theorem sub1128 (p : Pattern) : d101 (change p 48 none) = d101 p := by
  change (if p 115 then d100 (change p 48 none) else d98 (change p 48 none)) = d101 p
  rw [sub1127, sub1125]
  rfl
theorem sub1129 (p : Pattern) : d1 (change p 48 none) = d1 p := by
  rfl
theorem sub1130 (p : Pattern) : d102 (change p 48 none) = d102 p := by
  change (if p 247 then d12 (change p 48 none) else d1 (change p 48 none)) = d102 p
  rw [sub1033, sub1129]
  rfl
theorem sub1131 (p : Pattern) : d103 (change p 48 none) = d103 p := by
  change (if p 246 then d102 (change p 48 none) else d1 (change p 48 none)) = d103 p
  rw [sub1130, sub1129]
  rfl
theorem sub1132 (p : Pattern) : d104 (change p 48 none) = d104 p := by
  change (if p 204 then d12 (change p 48 none) else d103 (change p 48 none)) = d104 p
  rw [sub1033, sub1131]
  rfl
theorem sub1133 (p : Pattern) : d105 (change p 48 none) = d105 p := by
  change (if p 182 then d104 (change p 48 none) else d103 (change p 48 none)) = d105 p
  rw [sub1132, sub1131]
  rfl
theorem sub1134 (p : Pattern) : d5 (change p 48 none) = d5 p := by
  rfl
theorem sub1135 (p : Pattern) : d106 (change p 48 none) = d106 p := by
  change (if p 247 then d12 (change p 48 none) else d5 (change p 48 none)) = d106 p
  rw [sub1033, sub1134]
  rfl
theorem sub1136 (p : Pattern) : d107 (change p 48 none) = d107 p := by
  change (if p 246 then d106 (change p 48 none) else d5 (change p 48 none)) = d107 p
  rw [sub1135, sub1134]
  rfl
theorem sub1137 (p : Pattern) : d108 (change p 48 none) = d108 p := by
  change (if p 204 then d12 (change p 48 none) else d107 (change p 48 none)) = d108 p
  rw [sub1033, sub1136]
  rfl
theorem sub1138 (p : Pattern) : d109 (change p 48 none) = d109 p := by
  change (if p 182 then d108 (change p 48 none) else d107 (change p 48 none)) = d109 p
  rw [sub1137, sub1136]
  rfl
theorem sub1139 (p : Pattern) : d110 (change p 48 none) = d110 p := by
  change (if p 163 then d109 (change p 48 none) else d105 (change p 48 none)) = d110 p
  rw [sub1138, sub1133]
  rfl
theorem sub1140 (p : Pattern) : d111 (change p 48 none) = d111 p := by
  change (if p 162 then d110 (change p 48 none) else d105 (change p 48 none)) = d111 p
  rw [sub1139, sub1133]
  rfl
theorem sub1141 (p : Pattern) : d112 (change p 48 none) = d112 p := by
  change (if p 163 then d12 (change p 48 none) else d60 (change p 48 none)) = d112 p
  rw [sub1033, sub1087]
  rfl
theorem sub1142 (p : Pattern) : d113 (change p 48 none) = d113 p := by
  change (if p 162 then d112 (change p 48 none) else d110 (change p 48 none)) = d113 p
  rw [sub1141, sub1139]
  rfl
theorem sub1143 (p : Pattern) : d114 (change p 48 none) = d114 p := by
  change (if p 161 then d113 (change p 48 none) else d111 (change p 48 none)) = d114 p
  rw [sub1142, sub1140]
  rfl
theorem sub1144 (p : Pattern) : d3 (change p 48 none) = d3 p := by
  rfl
theorem sub1145 (p : Pattern) : d115 (change p 48 none) = d115 p := by
  change (if p 247 then d12 (change p 48 none) else d3 (change p 48 none)) = d115 p
  rw [sub1033, sub1144]
  rfl
theorem sub1146 (p : Pattern) : d116 (change p 48 none) = d116 p := by
  change (if p 246 then d115 (change p 48 none) else d3 (change p 48 none)) = d116 p
  rw [sub1145, sub1144]
  rfl
theorem sub1147 (p : Pattern) : d117 (change p 48 none) = d117 p := by
  change (if p 204 then d12 (change p 48 none) else d116 (change p 48 none)) = d117 p
  rw [sub1033, sub1146]
  rfl
theorem sub1148 (p : Pattern) : d118 (change p 48 none) = d118 p := by
  change (if p 182 then d117 (change p 48 none) else d103 (change p 48 none)) = d118 p
  rw [sub1147, sub1131]
  rfl
theorem sub1149 (p : Pattern) : d7 (change p 48 none) = d7 p := by
  rfl
theorem sub1150 (p : Pattern) : d119 (change p 48 none) = d119 p := by
  change (if p 247 then d12 (change p 48 none) else d7 (change p 48 none)) = d119 p
  rw [sub1033, sub1149]
  rfl
theorem sub1151 (p : Pattern) : d120 (change p 48 none) = d120 p := by
  change (if p 246 then d119 (change p 48 none) else d7 (change p 48 none)) = d120 p
  rw [sub1150, sub1149]
  rfl
theorem sub1152 (p : Pattern) : d121 (change p 48 none) = d121 p := by
  change (if p 204 then d12 (change p 48 none) else d120 (change p 48 none)) = d121 p
  rw [sub1033, sub1151]
  rfl
theorem sub1153 (p : Pattern) : d122 (change p 48 none) = d122 p := by
  change (if p 182 then d121 (change p 48 none) else d103 (change p 48 none)) = d122 p
  rw [sub1152, sub1131]
  rfl
theorem sub1154 (p : Pattern) : d123 (change p 48 none) = d123 p := by
  change (if p 163 then d122 (change p 48 none) else d118 (change p 48 none)) = d123 p
  rw [sub1153, sub1148]
  rfl
theorem sub1155 (p : Pattern) : d124 (change p 48 none) = d124 p := by
  change (if p 182 then d12 (change p 48 none) else d103 (change p 48 none)) = d124 p
  rw [sub1033, sub1131]
  rfl
theorem sub1156 (p : Pattern) : d125 (change p 48 none) = d125 p := by
  change (if p 182 then d12 (change p 48 none) else d107 (change p 48 none)) = d125 p
  rw [sub1033, sub1136]
  rfl
theorem sub1157 (p : Pattern) : d126 (change p 48 none) = d126 p := by
  change (if p 163 then d125 (change p 48 none) else d124 (change p 48 none)) = d126 p
  rw [sub1156, sub1155]
  rfl
theorem sub1158 (p : Pattern) : d127 (change p 48 none) = d127 p := by
  change (if p 162 then d126 (change p 48 none) else d123 (change p 48 none)) = d127 p
  rw [sub1157, sub1154]
  rfl
theorem sub1159 (p : Pattern) : d128 (change p 48 none) = d128 p := by
  change (if p 163 then d12 (change p 48 none) else d70 (change p 48 none)) = d128 p
  rw [sub1033, sub1097]
  rfl
theorem sub1160 (p : Pattern) : d129 (change p 48 none) = d129 p := by
  change (if p 162 then d128 (change p 48 none) else d126 (change p 48 none)) = d129 p
  rw [sub1159, sub1157]
  rfl
theorem sub1161 (p : Pattern) : d130 (change p 48 none) = d130 p := by
  change (if p 161 then d129 (change p 48 none) else d127 (change p 48 none)) = d130 p
  rw [sub1160, sub1158]
  rfl
theorem sub1162 (p : Pattern) : d131 (change p 48 none) = d131 p := by
  change (if p 160 then d130 (change p 48 none) else d114 (change p 48 none)) = d131 p
  rw [sub1161, sub1143]
  rfl
theorem sub1163 (p : Pattern) : d132 (change p 48 none) = d132 p := by
  change (if p 182 then d117 (change p 48 none) else d116 (change p 48 none)) = d132 p
  rw [sub1147, sub1146]
  rfl
theorem sub1164 (p : Pattern) : d133 (change p 48 none) = d133 p := by
  change (if p 163 then d132 (change p 48 none) else d105 (change p 48 none)) = d133 p
  rw [sub1163, sub1133]
  rfl
theorem sub1165 (p : Pattern) : d134 (change p 48 none) = d134 p := by
  change (if p 163 then d60 (change p 48 none) else d109 (change p 48 none)) = d134 p
  rw [sub1087, sub1138]
  rfl
theorem sub1166 (p : Pattern) : d135 (change p 48 none) = d135 p := by
  change (if p 162 then d134 (change p 48 none) else d133 (change p 48 none)) = d135 p
  rw [sub1165, sub1164]
  rfl
theorem sub1167 (p : Pattern) : d136 (change p 48 none) = d136 p := by
  change (if p 163 then d62 (change p 48 none) else d109 (change p 48 none)) = d136 p
  rw [sub1089, sub1138]
  rfl
theorem sub1168 (p : Pattern) : d137 (change p 48 none) = d137 p := by
  change (if p 162 then d12 (change p 48 none) else d136 (change p 48 none)) = d137 p
  rw [sub1033, sub1167]
  rfl
theorem sub1169 (p : Pattern) : d138 (change p 48 none) = d138 p := by
  change (if p 161 then d137 (change p 48 none) else d135 (change p 48 none)) = d138 p
  rw [sub1168, sub1166]
  rfl
theorem sub1170 (p : Pattern) : d139 (change p 48 none) = d139 p := by
  change (if p 182 then d12 (change p 48 none) else d116 (change p 48 none)) = d139 p
  rw [sub1033, sub1146]
  rfl
theorem sub1171 (p : Pattern) : d140 (change p 48 none) = d140 p := by
  change (if p 163 then d139 (change p 48 none) else d122 (change p 48 none)) = d140 p
  rw [sub1170, sub1153]
  rfl
theorem sub1172 (p : Pattern) : d141 (change p 48 none) = d141 p := by
  change (if p 163 then d70 (change p 48 none) else d125 (change p 48 none)) = d141 p
  rw [sub1097, sub1156]
  rfl
theorem sub1173 (p : Pattern) : d142 (change p 48 none) = d142 p := by
  change (if p 162 then d141 (change p 48 none) else d140 (change p 48 none)) = d142 p
  rw [sub1172, sub1171]
  rfl
theorem sub1174 (p : Pattern) : d143 (change p 48 none) = d143 p := by
  change (if p 163 then d72 (change p 48 none) else d125 (change p 48 none)) = d143 p
  rw [sub1099, sub1156]
  rfl
theorem sub1175 (p : Pattern) : d144 (change p 48 none) = d144 p := by
  change (if p 162 then d12 (change p 48 none) else d143 (change p 48 none)) = d144 p
  rw [sub1033, sub1174]
  rfl
theorem sub1176 (p : Pattern) : d145 (change p 48 none) = d145 p := by
  change (if p 161 then d144 (change p 48 none) else d142 (change p 48 none)) = d145 p
  rw [sub1175, sub1173]
  rfl
theorem sub1177 (p : Pattern) : d146 (change p 48 none) = d146 p := by
  change (if p 160 then d145 (change p 48 none) else d138 (change p 48 none)) = d146 p
  rw [sub1176, sub1169]
  rfl
theorem sub1178 (p : Pattern) : d147 (change p 48 none) = d147 p := by
  change (if p 141 then d146 (change p 48 none) else d131 (change p 48 none)) = d147 p
  rw [sub1177, sub1162]
  rfl
theorem sub1179 (p : Pattern) : d148 (change p 48 none) = d148 p := by
  change (if p 182 then d121 (change p 48 none) else d120 (change p 48 none)) = d148 p
  rw [sub1152, sub1151]
  rfl
theorem sub1180 (p : Pattern) : d149 (change p 48 none) = d149 p := by
  change (if p 163 then d148 (change p 48 none) else d132 (change p 48 none)) = d149 p
  rw [sub1179, sub1163]
  rfl
theorem sub1181 (p : Pattern) : d150 (change p 48 none) = d150 p := by
  change (if p 162 then d12 (change p 48 none) else d149 (change p 48 none)) = d150 p
  rw [sub1033, sub1180]
  rfl
theorem sub1182 (p : Pattern) : d151 (change p 48 none) = d151 p := by
  change (if p 161 then d12 (change p 48 none) else d150 (change p 48 none)) = d151 p
  rw [sub1033, sub1181]
  rfl
theorem sub1183 (p : Pattern) : d152 (change p 48 none) = d152 p := by
  change (if p 160 then d151 (change p 48 none) else d114 (change p 48 none)) = d152 p
  rw [sub1182, sub1143]
  rfl
theorem sub1184 (p : Pattern) : d153 (change p 48 none) = d153 p := by
  change (if p 163 then d12 (change p 48 none) else d148 (change p 48 none)) = d153 p
  rw [sub1033, sub1179]
  rfl
theorem sub1185 (p : Pattern) : d154 (change p 48 none) = d154 p := by
  change (if p 162 then d12 (change p 48 none) else d153 (change p 48 none)) = d154 p
  rw [sub1033, sub1184]
  rfl
theorem sub1186 (p : Pattern) : d155 (change p 48 none) = d155 p := by
  change (if p 161 then d12 (change p 48 none) else d154 (change p 48 none)) = d155 p
  rw [sub1033, sub1185]
  rfl
theorem sub1187 (p : Pattern) : d156 (change p 48 none) = d156 p := by
  change (if p 160 then d155 (change p 48 none) else d138 (change p 48 none)) = d156 p
  rw [sub1186, sub1169]
  rfl
theorem sub1188 (p : Pattern) : d157 (change p 48 none) = d157 p := by
  change (if p 141 then d156 (change p 48 none) else d152 (change p 48 none)) = d157 p
  rw [sub1187, sub1183]
  rfl
theorem sub1189 (p : Pattern) : d158 (change p 48 none) = d158 p := by
  change (if p 138 then d157 (change p 48 none) else d147 (change p 48 none)) = d158 p
  rw [sub1188, sub1178]
  rfl
theorem sub1190 (p : Pattern) : d159 (change p 48 none) = d159 p := by
  change (if p 162 then d12 (change p 48 none) else d112 (change p 48 none)) = d159 p
  rw [sub1033, sub1141]
  rfl
theorem sub1191 (p : Pattern) : d160 (change p 48 none) = d160 p := by
  change (if p 161 then d12 (change p 48 none) else d159 (change p 48 none)) = d160 p
  rw [sub1033, sub1190]
  rfl
theorem sub1192 (p : Pattern) : d161 (change p 48 none) = d161 p := by
  change (if p 160 then d12 (change p 48 none) else d160 (change p 48 none)) = d161 p
  rw [sub1033, sub1191]
  rfl
theorem sub1193 (p : Pattern) : d162 (change p 48 none) = d162 p := by
  change (if p 141 then d12 (change p 48 none) else d161 (change p 48 none)) = d162 p
  rw [sub1033, sub1192]
  rfl
theorem sub1194 (p : Pattern) : d163 (change p 48 none) = d163 p := by
  change (if p 138 then d162 (change p 48 none) else d157 (change p 48 none)) = d163 p
  rw [sub1193, sub1188]
  rfl
theorem sub1195 (p : Pattern) : d164 (change p 48 none) = d164 p := by
  change (if p 116 then d163 (change p 48 none) else d158 (change p 48 none)) = d164 p
  rw [sub1194, sub1189]
  rfl
theorem sub1196 (p : Pattern) : d165 (change p 48 none) = d165 p := by
  change (if p 138 then d12 (change p 48 none) else d157 (change p 48 none)) = d165 p
  rw [sub1033, sub1188]
  rfl
theorem sub1197 (p : Pattern) : d166 (change p 48 none) = d166 p := by
  change (if p 116 then d165 (change p 48 none) else d158 (change p 48 none)) = d166 p
  rw [sub1196, sub1189]
  rfl
theorem sub1198 (p : Pattern) : d167 (change p 48 none) = d167 p := by
  change (if p 115 then d166 (change p 48 none) else d164 (change p 48 none)) = d167 p
  rw [sub1197, sub1195]
  rfl
theorem sub1199 (p : Pattern) : d168 (change p 48 none) = d168 p := by
  change (if p 71 then d167 (change p 48 none) else d101 (change p 48 none)) = d168 p
  rw [sub1198, sub1128]
  rfl
end NetHack.Sokoban22Refined85
