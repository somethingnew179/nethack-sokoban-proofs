/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions06
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s1050 (pattern : Ten) : d49 (change pattern 4 2) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 4 2) else d43 (change pattern 4 2)) = d49 pattern
  rw [s1045, s1049]
  rfl
theorem s1051 (pattern : Ten) : d54 (change pattern 4 2) = d54 pattern := by
  change (if pattern.h then d49 (change pattern 4 2) else d48 (change pattern 4 2)) = d54 pattern
  rw [s1050, s1047]
  rfl
theorem s1052 (pattern : Ten) : d134 (change pattern 4 2) = d54 pattern := by
  change d54 (change pattern 4 2) = d54 pattern
  exact s1051 pattern
theorem s1053 (pattern : Ten) : d7 (change pattern 4 2) = d7 pattern := by
  rfl
theorem s1054 (pattern : Ten) : d8 (change pattern 4 2) = d8 pattern := by
  rfl
theorem s1055 (pattern : Ten) : d38 (change pattern 4 2) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 4 2) else d7 (change pattern 4 2)) = d38 pattern
  rw [s1054, s1053]
  rfl
theorem s1056 (pattern : Ten) : d40 (change pattern 4 2) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 4 2) else d38 (change pattern 4 2)) = d40 pattern
  rw [s1054, s1055]
  rfl
theorem s1057 (pattern : Ten) : d46 (change pattern 4 2) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 4 2) else d40 (change pattern 4 2)) = d46 pattern
  rw [s1045, s1056]
  rfl
theorem s1058 (pattern : Ten) : d52 (change pattern 4 2) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 4 2) else d46 (change pattern 4 2)) = d52 pattern
  rw [s1045, s1057]
  rfl
theorem s1059 (pattern : Ten) : d56 (change pattern 4 2) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 4 2) else d52 (change pattern 4 2)) = d56 pattern
  rw [s1045, s1058]
  rfl
theorem s1060 (pattern : Ten) : d135 (change pattern 4 2) = d556 pattern := by
  change (if pattern.d then d56 (change pattern 4 2) else d134 (change pattern 4 2)) = d556 pattern
  rw [s1059, s1052]
  rfl
theorem s1061 (pattern : Ten) : d1 (change pattern 4 2) = d1 pattern := by
  rfl
theorem s1062 (pattern : Ten) : d171 (change pattern 4 2) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 4 2) else d0 (change pattern 4 2)) = d171 pattern
  rw [s1061, s1041]
  rfl
theorem s1063 (pattern : Ten) : d3 (change pattern 4 2) = d3 pattern := by
  rfl
theorem s1064 (pattern : Ten) : d172 (change pattern 4 2) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 4 2) else d2 (change pattern 4 2)) = d172 pattern
  rw [s1063, s1042]
  rfl
theorem s1065 (pattern : Ten) : d174 (change pattern 4 2) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 4 2) else d171 (change pattern 4 2)) = d174 pattern
  rw [s1064, s1062]
  rfl
theorem s1066 (pattern : Ten) : d5 (change pattern 4 2) = d5 pattern := by
  rfl
theorem s1067 (pattern : Ten) : d193 (change pattern 4 2) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 4 2) else d4 (change pattern 4 2)) = d193 pattern
  rw [s1066, s1044]
  rfl
theorem s1068 (pattern : Ten) : d197 (change pattern 4 2) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 4 2) else d193 (change pattern 4 2)) = d197 pattern
  rw [s1045, s1067]
  rfl
theorem s1069 (pattern : Ten) : d202 (change pattern 4 2) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 4 2) else d174 (change pattern 4 2)) = d202 pattern
  rw [s1068, s1065]
  rfl
theorem s1070 (pattern : Ten) : d194 (change pattern 4 2) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 4 2) else d6 (change pattern 4 2)) = d194 pattern
  rw [s1053, s1048]
  rfl
theorem s1071 (pattern : Ten) : d198 (change pattern 4 2) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 4 2) else d194 (change pattern 4 2)) = d198 pattern
  rw [s1045, s1070]
  rfl
theorem s1072 (pattern : Ten) : d203 (change pattern 4 2) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 4 2) else d198 (change pattern 4 2)) = d203 pattern
  rw [s1045, s1071]
  rfl
theorem s1073 (pattern : Ten) : d207 (change pattern 4 2) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 4 2) else d202 (change pattern 4 2)) = d207 pattern
  rw [s1072, s1069]
  rfl
theorem s1074 (pattern : Ten) : d290 (change pattern 4 2) = d207 pattern := by
  change d207 (change pattern 4 2) = d207 pattern
  exact s1073 pattern
theorem s1075 (pattern : Ten) : d9 (change pattern 4 2) = d9 pattern := by
  rfl
theorem s1076 (pattern : Ten) : d195 (change pattern 4 2) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 4 2) else d8 (change pattern 4 2)) = d195 pattern
  rw [s1075, s1054]
  rfl
theorem s1077 (pattern : Ten) : d200 (change pattern 4 2) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 4 2) else d195 (change pattern 4 2)) = d200 pattern
  rw [s1045, s1076]
  rfl
theorem s1078 (pattern : Ten) : d205 (change pattern 4 2) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 4 2) else d200 (change pattern 4 2)) = d205 pattern
  rw [s1045, s1077]
  rfl
theorem s1079 (pattern : Ten) : d209 (change pattern 4 2) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 4 2) else d205 (change pattern 4 2)) = d209 pattern
  rw [s1045, s1078]
  rfl
theorem s1080 (pattern : Ten) : d291 (change pattern 4 2) = d560 pattern := by
  change (if pattern.d then d209 (change pattern 4 2) else d290 (change pattern 4 2)) = d560 pattern
  rw [s1079, s1074]
  rfl
theorem s1081 (pattern : Ten) : d0 (change pattern 4 5) = d0 pattern := by
  rfl
theorem s1082 (pattern : Ten) : d1 (change pattern 4 5) = d1 pattern := by
  rfl
theorem s1083 (pattern : Ten) : d171 (change pattern 4 5) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 4 5) else d0 (change pattern 4 5)) = d171 pattern
  rw [s1082, s1081]
  rfl
theorem s1084 (pattern : Ten) : d2 (change pattern 4 5) = d2 pattern := by
  rfl
theorem s1085 (pattern : Ten) : d3 (change pattern 4 5) = d3 pattern := by
  rfl
theorem s1086 (pattern : Ten) : d172 (change pattern 4 5) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 4 5) else d2 (change pattern 4 5)) = d172 pattern
  rw [s1085, s1084]
  rfl
theorem s1087 (pattern : Ten) : d174 (change pattern 4 5) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 4 5) else d171 (change pattern 4 5)) = d174 pattern
  rw [s1086, s1083]
  rfl
theorem s1088 (pattern : Ten) : d4 (change pattern 4 5) = d4 pattern := by
  rfl
theorem s1089 (pattern : Ten) : d5 (change pattern 4 5) = d5 pattern := by
  rfl
theorem s1090 (pattern : Ten) : d193 (change pattern 4 5) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 4 5) else d4 (change pattern 4 5)) = d193 pattern
  rw [s1089, s1088]
  rfl
theorem s1091 (pattern : Ten) : d10 (change pattern 4 5) = d10 pattern := by
  rfl
theorem s1092 (pattern : Ten) : d197 (change pattern 4 5) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 4 5) else d193 (change pattern 4 5)) = d197 pattern
  rw [s1091, s1090]
  rfl
theorem s1093 (pattern : Ten) : d202 (change pattern 4 5) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 4 5) else d174 (change pattern 4 5)) = d202 pattern
  rw [s1092, s1087]
  rfl
theorem s1094 (pattern : Ten) : d6 (change pattern 4 5) = d6 pattern := by
  rfl
theorem s1095 (pattern : Ten) : d7 (change pattern 4 5) = d7 pattern := by
  rfl
theorem s1096 (pattern : Ten) : d194 (change pattern 4 5) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 4 5) else d6 (change pattern 4 5)) = d194 pattern
  rw [s1095, s1094]
  rfl
theorem s1097 (pattern : Ten) : d198 (change pattern 4 5) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 4 5) else d194 (change pattern 4 5)) = d198 pattern
  rw [s1091, s1096]
  rfl
theorem s1098 (pattern : Ten) : d203 (change pattern 4 5) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 4 5) else d198 (change pattern 4 5)) = d203 pattern
  rw [s1091, s1097]
  rfl
theorem s1099 (pattern : Ten) : d207 (change pattern 4 5) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 4 5) else d202 (change pattern 4 5)) = d207 pattern
  rw [s1098, s1093]
  rfl
theorem s1100 (pattern : Ten) : d290 (change pattern 4 5) = d207 pattern := by
  change d207 (change pattern 4 5) = d207 pattern
  exact s1099 pattern
theorem s1101 (pattern : Ten) : d8 (change pattern 4 5) = d8 pattern := by
  rfl
theorem s1102 (pattern : Ten) : d9 (change pattern 4 5) = d9 pattern := by
  rfl
theorem s1103 (pattern : Ten) : d195 (change pattern 4 5) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 4 5) else d8 (change pattern 4 5)) = d195 pattern
  rw [s1102, s1101]
  rfl
theorem s1104 (pattern : Ten) : d200 (change pattern 4 5) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 4 5) else d195 (change pattern 4 5)) = d200 pattern
  rw [s1091, s1103]
  rfl
theorem s1105 (pattern : Ten) : d205 (change pattern 4 5) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 4 5) else d200 (change pattern 4 5)) = d205 pattern
  rw [s1091, s1104]
  rfl
theorem s1106 (pattern : Ten) : d209 (change pattern 4 5) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 4 5) else d205 (change pattern 4 5)) = d209 pattern
  rw [s1091, s1105]
  rfl
theorem s1107 (pattern : Ten) : d291 (change pattern 4 5) = d560 pattern := by
  change (if pattern.d then d209 (change pattern 4 5) else d290 (change pattern 4 5)) = d560 pattern
  rw [s1106, s1100]
  rfl
theorem s1108 (pattern : Ten) : d0 (change pattern 4 6) = d0 pattern := by
  rfl
theorem s1109 (pattern : Ten) : d2 (change pattern 4 6) = d2 pattern := by
  rfl
theorem s1110 (pattern : Ten) : d15 (change pattern 4 6) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 4 6) else d0 (change pattern 4 6)) = d15 pattern
  rw [s1109, s1108]
  rfl
theorem s1111 (pattern : Ten) : d4 (change pattern 4 6) = d4 pattern := by
  rfl
theorem s1112 (pattern : Ten) : d10 (change pattern 4 6) = d10 pattern := by
  rfl
theorem s1113 (pattern : Ten) : d42 (change pattern 4 6) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 4 6) else d4 (change pattern 4 6)) = d42 pattern
  rw [s1112, s1111]
  rfl
theorem s1114 (pattern : Ten) : d48 (change pattern 4 6) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 4 6) else d15 (change pattern 4 6)) = d48 pattern
  rw [s1113, s1110]
  rfl
theorem s1115 (pattern : Ten) : d6 (change pattern 4 6) = d6 pattern := by
  rfl
theorem s1116 (pattern : Ten) : d43 (change pattern 4 6) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 4 6) else d6 (change pattern 4 6)) = d43 pattern
  rw [s1112, s1115]
  rfl
theorem s1117 (pattern : Ten) : d49 (change pattern 4 6) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 4 6) else d43 (change pattern 4 6)) = d49 pattern
  rw [s1112, s1116]
  rfl
theorem s1118 (pattern : Ten) : d54 (change pattern 4 6) = d54 pattern := by
  change (if pattern.h then d49 (change pattern 4 6) else d48 (change pattern 4 6)) = d54 pattern
  rw [s1117, s1114]
  rfl
theorem s1119 (pattern : Ten) : d134 (change pattern 4 6) = d54 pattern := by
  change d54 (change pattern 4 6) = d54 pattern
  exact s1118 pattern
theorem s1120 (pattern : Ten) : d7 (change pattern 4 6) = d7 pattern := by
  rfl
theorem s1121 (pattern : Ten) : d8 (change pattern 4 6) = d8 pattern := by
  rfl
theorem s1122 (pattern : Ten) : d38 (change pattern 4 6) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 4 6) else d7 (change pattern 4 6)) = d38 pattern
  rw [s1121, s1120]
  rfl
theorem s1123 (pattern : Ten) : d40 (change pattern 4 6) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 4 6) else d38 (change pattern 4 6)) = d40 pattern
  rw [s1121, s1122]
  rfl
theorem s1124 (pattern : Ten) : d46 (change pattern 4 6) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 4 6) else d40 (change pattern 4 6)) = d46 pattern
  rw [s1112, s1123]
  rfl
theorem s1125 (pattern : Ten) : d52 (change pattern 4 6) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 4 6) else d46 (change pattern 4 6)) = d52 pattern
  rw [s1112, s1124]
  rfl
theorem s1126 (pattern : Ten) : d56 (change pattern 4 6) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 4 6) else d52 (change pattern 4 6)) = d56 pattern
  rw [s1112, s1125]
  rfl
theorem s1127 (pattern : Ten) : d135 (change pattern 4 6) = d556 pattern := by
  change (if pattern.d then d56 (change pattern 4 6) else d134 (change pattern 4 6)) = d556 pattern
  rw [s1126, s1119]
  rfl
theorem s1128 (pattern : Ten) : d1 (change pattern 4 6) = d1 pattern := by
  rfl
theorem s1129 (pattern : Ten) : d171 (change pattern 4 6) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 4 6) else d0 (change pattern 4 6)) = d171 pattern
  rw [s1128, s1108]
  rfl
theorem s1130 (pattern : Ten) : d3 (change pattern 4 6) = d3 pattern := by
  rfl
theorem s1131 (pattern : Ten) : d172 (change pattern 4 6) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 4 6) else d2 (change pattern 4 6)) = d172 pattern
  rw [s1130, s1109]
  rfl
theorem s1132 (pattern : Ten) : d174 (change pattern 4 6) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 4 6) else d171 (change pattern 4 6)) = d174 pattern
  rw [s1131, s1129]
  rfl
theorem s1133 (pattern : Ten) : d5 (change pattern 4 6) = d5 pattern := by
  rfl
theorem s1134 (pattern : Ten) : d193 (change pattern 4 6) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 4 6) else d4 (change pattern 4 6)) = d193 pattern
  rw [s1133, s1111]
  rfl
theorem s1135 (pattern : Ten) : d197 (change pattern 4 6) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 4 6) else d193 (change pattern 4 6)) = d197 pattern
  rw [s1112, s1134]
  rfl
theorem s1136 (pattern : Ten) : d202 (change pattern 4 6) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 4 6) else d174 (change pattern 4 6)) = d202 pattern
  rw [s1135, s1132]
  rfl
theorem s1137 (pattern : Ten) : d194 (change pattern 4 6) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 4 6) else d6 (change pattern 4 6)) = d194 pattern
  rw [s1120, s1115]
  rfl
theorem s1138 (pattern : Ten) : d198 (change pattern 4 6) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 4 6) else d194 (change pattern 4 6)) = d198 pattern
  rw [s1112, s1137]
  rfl
theorem s1139 (pattern : Ten) : d203 (change pattern 4 6) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 4 6) else d198 (change pattern 4 6)) = d203 pattern
  rw [s1112, s1138]
  rfl
theorem s1140 (pattern : Ten) : d207 (change pattern 4 6) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 4 6) else d202 (change pattern 4 6)) = d207 pattern
  rw [s1139, s1136]
  rfl
theorem s1141 (pattern : Ten) : d290 (change pattern 4 6) = d207 pattern := by
  change d207 (change pattern 4 6) = d207 pattern
  exact s1140 pattern
theorem s1142 (pattern : Ten) : d9 (change pattern 4 6) = d9 pattern := by
  rfl
theorem s1143 (pattern : Ten) : d195 (change pattern 4 6) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 4 6) else d8 (change pattern 4 6)) = d195 pattern
  rw [s1142, s1121]
  rfl
theorem s1144 (pattern : Ten) : d200 (change pattern 4 6) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 4 6) else d195 (change pattern 4 6)) = d200 pattern
  rw [s1112, s1143]
  rfl
theorem s1145 (pattern : Ten) : d205 (change pattern 4 6) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 4 6) else d200 (change pattern 4 6)) = d205 pattern
  rw [s1112, s1144]
  rfl
theorem s1146 (pattern : Ten) : d209 (change pattern 4 6) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 4 6) else d205 (change pattern 4 6)) = d209 pattern
  rw [s1112, s1145]
  rfl
theorem s1147 (pattern : Ten) : d291 (change pattern 4 6) = d560 pattern := by
  change (if pattern.d then d209 (change pattern 4 6) else d290 (change pattern 4 6)) = d560 pattern
  rw [s1146, s1141]
  rfl
theorem s1148 (pattern : Ten) : d7 (change pattern 4 3) = d7 pattern := by
  rfl
theorem s1149 (pattern : Ten) : d8 (change pattern 4 3) = d8 pattern := by
  rfl
theorem s1150 (pattern : Ten) : d38 (change pattern 4 3) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 4 3) else d7 (change pattern 4 3)) = d38 pattern
  rw [s1149, s1148]
  rfl
theorem s1151 (pattern : Ten) : d40 (change pattern 4 3) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 4 3) else d38 (change pattern 4 3)) = d40 pattern
  rw [s1149, s1150]
  rfl
theorem s1152 (pattern : Ten) : d10 (change pattern 4 3) = d10 pattern := by
  rfl
theorem s1153 (pattern : Ten) : d46 (change pattern 4 3) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 4 3) else d40 (change pattern 4 3)) = d46 pattern
  rw [s1152, s1151]
  rfl
theorem s1154 (pattern : Ten) : d52 (change pattern 4 3) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 4 3) else d46 (change pattern 4 3)) = d52 pattern
  rw [s1152, s1153]
  rfl
theorem s1155 (pattern : Ten) : d56 (change pattern 4 3) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 4 3) else d52 (change pattern 4 3)) = d56 pattern
  rw [s1152, s1154]
  rfl
theorem s1156 (pattern : Ten) : d135 (change pattern 4 3) = d56 pattern := by
  change d56 (change pattern 4 3) = d56 pattern
  exact s1155 pattern
theorem s1157 (pattern : Ten) : d9 (change pattern 4 3) = d9 pattern := by
  rfl
theorem s1158 (pattern : Ten) : d195 (change pattern 4 3) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 4 3) else d8 (change pattern 4 3)) = d195 pattern
  rw [s1157, s1149]
  rfl
theorem s1159 (pattern : Ten) : d200 (change pattern 4 3) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 4 3) else d195 (change pattern 4 3)) = d200 pattern
  rw [s1152, s1158]
  rfl
theorem s1160 (pattern : Ten) : d205 (change pattern 4 3) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 4 3) else d200 (change pattern 4 3)) = d205 pattern
  rw [s1152, s1159]
  rfl
theorem s1161 (pattern : Ten) : d209 (change pattern 4 3) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 4 3) else d205 (change pattern 4 3)) = d209 pattern
  rw [s1152, s1160]
  rfl
theorem s1162 (pattern : Ten) : d291 (change pattern 4 3) = d209 pattern := by
  change d209 (change pattern 4 3) = d209 pattern
  exact s1161 pattern
theorem s1163 (pattern : Ten) : d0 (change pattern 5 10) = d0 pattern := by
  rfl
theorem s1164 (pattern : Ten) : d1 (change pattern 5 10) = d1 pattern := by
  rfl
theorem s1165 (pattern : Ten) : d171 (change pattern 5 10) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 5 10) else d0 (change pattern 5 10)) = d171 pattern
  rw [s1164, s1163]
  rfl
theorem s1166 (pattern : Ten) : d292 (change pattern 5 10) = d171 pattern := by
  change d171 (change pattern 5 10) = d171 pattern
  exact s1165 pattern
theorem s1167 (pattern : Ten) : d2 (change pattern 5 10) = d2 pattern := by
  rfl
theorem s1168 (pattern : Ten) : d3 (change pattern 5 10) = d3 pattern := by
  rfl
theorem s1169 (pattern : Ten) : d172 (change pattern 5 10) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 5 10) else d2 (change pattern 5 10)) = d172 pattern
  rw [s1168, s1167]
  rfl
theorem s1170 (pattern : Ten) : d293 (change pattern 5 10) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 5 10) else d292 (change pattern 5 10)) = d174 pattern
  rw [s1169, s1166]
  rfl
theorem s1171 (pattern : Ten) : d4 (change pattern 5 10) = d4 pattern := by
  rfl
theorem s1172 (pattern : Ten) : d5 (change pattern 5 10) = d5 pattern := by
  rfl
theorem s1173 (pattern : Ten) : d193 (change pattern 5 10) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 5 10) else d4 (change pattern 5 10)) = d193 pattern
  rw [s1172, s1171]
  rfl
theorem s1174 (pattern : Ten) : d10 (change pattern 5 10) = d10 pattern := by
  rfl
theorem s1175 (pattern : Ten) : d197 (change pattern 5 10) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 5 10) else d193 (change pattern 5 10)) = d197 pattern
  rw [s1174, s1173]
  rfl
theorem s1176 (pattern : Ten) : d294 (change pattern 5 10) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 5 10) else d293 (change pattern 5 10)) = d202 pattern
  rw [s1175, s1170]
  rfl
theorem s1177 (pattern : Ten) : d6 (change pattern 5 10) = d6 pattern := by
  rfl
theorem s1178 (pattern : Ten) : d7 (change pattern 5 10) = d7 pattern := by
  rfl
theorem s1179 (pattern : Ten) : d194 (change pattern 5 10) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 5 10) else d6 (change pattern 5 10)) = d194 pattern
  rw [s1178, s1177]
  rfl
theorem s1180 (pattern : Ten) : d198 (change pattern 5 10) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 5 10) else d194 (change pattern 5 10)) = d198 pattern
  rw [s1174, s1179]
  rfl
theorem s1181 (pattern : Ten) : d203 (change pattern 5 10) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 5 10) else d198 (change pattern 5 10)) = d203 pattern
  rw [s1174, s1180]
  rfl
theorem s1182 (pattern : Ten) : d295 (change pattern 5 10) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 5 10) else d294 (change pattern 5 10)) = d207 pattern
  rw [s1181, s1176]
  rfl
theorem s1183 (pattern : Ten) : d174 (change pattern 5 10) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 5 10) else d171 (change pattern 5 10)) = d174 pattern
  rw [s1169, s1165]
  rfl
theorem s1184 (pattern : Ten) : d202 (change pattern 5 10) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 5 10) else d174 (change pattern 5 10)) = d202 pattern
  rw [s1175, s1183]
  rfl
theorem s1185 (pattern : Ten) : d207 (change pattern 5 10) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 5 10) else d202 (change pattern 5 10)) = d207 pattern
  rw [s1181, s1184]
  rfl
theorem s1186 (pattern : Ten) : d296 (change pattern 5 10) = d207 pattern := by
  change (if pattern.g then d207 (change pattern 5 10) else d295 (change pattern 5 10)) = d207 pattern
  rw [s1185, s1182]
  simp only [ite_self]
theorem s1187 (pattern : Ten) : d297 (change pattern 5 10) = d207 pattern := by
  change (if pattern.c then d207 (change pattern 5 10) else d296 (change pattern 5 10)) = d207 pattern
  rw [s1185, s1186]
  simp only [ite_self]
theorem s1188 (pattern : Ten) : d211 (change pattern 5 10) = d211 pattern := by
  change (if pattern.g then d10 (change pattern 5 10) else d207 (change pattern 5 10)) = d211 pattern
  rw [s1174, s1185]
  rfl
theorem s1189 (pattern : Ten) : d199 (change pattern 5 10) = d199 pattern := by
  change (if pattern.j then d193 (change pattern 5 10) else d172 (change pattern 5 10)) = d199 pattern
  rw [s1173, s1169]
  rfl
theorem s1190 (pattern : Ten) : d204 (change pattern 5 10) = d204 pattern := by
  change (if pattern.i then d198 (change pattern 5 10) else d199 (change pattern 5 10)) = d204 pattern
  rw [s1180, s1189]
  rfl
theorem s1191 (pattern : Ten) : d8 (change pattern 5 10) = d8 pattern := by
  rfl
theorem s1192 (pattern : Ten) : d9 (change pattern 5 10) = d9 pattern := by
  rfl
theorem s1193 (pattern : Ten) : d195 (change pattern 5 10) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 5 10) else d8 (change pattern 5 10)) = d195 pattern
  rw [s1192, s1191]
  rfl
theorem s1194 (pattern : Ten) : d200 (change pattern 5 10) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 5 10) else d195 (change pattern 5 10)) = d200 pattern
  rw [s1174, s1193]
  rfl
theorem s1195 (pattern : Ten) : d205 (change pattern 5 10) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 5 10) else d200 (change pattern 5 10)) = d205 pattern
  rw [s1174, s1194]
  rfl
theorem s1196 (pattern : Ten) : d208 (change pattern 5 10) = d208 pattern := by
  change (if pattern.h then d205 (change pattern 5 10) else d204 (change pattern 5 10)) = d208 pattern
  rw [s1195, s1190]
  rfl
theorem s1197 (pattern : Ten) : d212 (change pattern 5 10) = d212 pattern := by
  change (if pattern.g then d10 (change pattern 5 10) else d208 (change pattern 5 10)) = d212 pattern
  rw [s1174, s1196]
  rfl
theorem s1198 (pattern : Ten) : d215 (change pattern 5 10) = d215 pattern := by
  change (if pattern.c then d212 (change pattern 5 10) else d211 (change pattern 5 10)) = d215 pattern
  rw [s1197, s1188]
  rfl
theorem s1199 (pattern : Ten) : d298 (change pattern 5 10) = d218 pattern := by
  change (if pattern.e then d215 (change pattern 5 10) else d297 (change pattern 5 10)) = d218 pattern
  rw [s1198, s1187]
  rfl
end NetHack.Sokoban41.Diagram
