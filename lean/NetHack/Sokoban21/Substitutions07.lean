/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions06
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s1050 (pattern : Twelve) : d1 (change pattern 7 8) = d1 pattern := by
  rfl
theorem s1051 (pattern : Twelve) : d26 (change pattern 7 8) = d1 pattern := by
  change d1 (change pattern 7 8) = d1 pattern
  exact s1050 pattern
theorem s1052 (pattern : Twelve) : d236 (change pattern 7 8) = d1 pattern := by
  change d26 (change pattern 7 8) = d1 pattern
  exact s1051 pattern
theorem s1053 (pattern : Twelve) : d256 (change pattern 7 8) = d1859 pattern := by
  change (if pattern.f then d236 (change pattern 7 8) else d235 (change pattern 7 8)) = d1859 pattern
  rw [s1052, s1049]
  rfl
theorem s1054 (pattern : Twelve) : d237 (change pattern 7 8) = d0 pattern := by
  change d0 (change pattern 7 8) = d0 pattern
  exact s1048 pattern
theorem s1055 (pattern : Twelve) : d2 (change pattern 7 8) = d2 pattern := by
  rfl
theorem s1056 (pattern : Twelve) : d8 (change pattern 7 8) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 7 8) else d1 (change pattern 7 8)) = d8 pattern
  rw [s1055, s1050]
  rfl
theorem s1057 (pattern : Twelve) : d3 (change pattern 7 8) = d3 pattern := by
  rfl
theorem s1058 (pattern : Twelve) : d9 (change pattern 7 8) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 7 8) else d2 (change pattern 7 8)) = d9 pattern
  rw [s1057, s1055]
  rfl
theorem s1059 (pattern : Twelve) : d18 (change pattern 7 8) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 7 8) else d8 (change pattern 7 8)) = d18 pattern
  rw [s1058, s1056]
  rfl
theorem s1060 (pattern : Twelve) : d28 (change pattern 7 8) = d18 pattern := by
  change d18 (change pattern 7 8) = d18 pattern
  exact s1059 pattern
theorem s1061 (pattern : Twelve) : d238 (change pattern 7 8) = d18 pattern := by
  change d28 (change pattern 7 8) = d18 pattern
  exact s1060 pattern
theorem s1062 (pattern : Twelve) : d257 (change pattern 7 8) = d1941 pattern := by
  change (if pattern.f then d238 (change pattern 7 8) else d237 (change pattern 7 8)) = d1941 pattern
  rw [s1061, s1054]
  rfl
theorem s1063 (pattern : Twelve) : d272 (change pattern 7 8) = d1942 pattern := by
  change (if pattern.e then d257 (change pattern 7 8) else d256 (change pattern 7 8)) = d1942 pattern
  rw [s1062, s1053]
  rfl
theorem s1064 (pattern : Twelve) : d30 (change pattern 7 8) = d2 pattern := by
  change d2 (change pattern 7 8) = d2 pattern
  exact s1055 pattern
theorem s1065 (pattern : Twelve) : d239 (change pattern 7 8) = d2 pattern := by
  change d30 (change pattern 7 8) = d2 pattern
  exact s1064 pattern
theorem s1066 (pattern : Twelve) : d240 (change pattern 7 8) = d2 pattern := by
  change d30 (change pattern 7 8) = d2 pattern
  exact s1064 pattern
theorem s1067 (pattern : Twelve) : d258 (change pattern 7 8) = d2 pattern := by
  change (if pattern.f then d240 (change pattern 7 8) else d239 (change pattern 7 8)) = d2 pattern
  rw [s1066, s1065]
  simp only [ite_self]
theorem s1068 (pattern : Twelve) : d23 (change pattern 7 8) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 7 8) else d2 (change pattern 7 8)) = d23 pattern
  rw [s1058, s1055]
  rfl
theorem s1069 (pattern : Twelve) : d34 (change pattern 7 8) = d23 pattern := by
  change d23 (change pattern 7 8) = d23 pattern
  exact s1068 pattern
theorem s1070 (pattern : Twelve) : d241 (change pattern 7 8) = d23 pattern := by
  change d34 (change pattern 7 8) = d23 pattern
  exact s1069 pattern
theorem s1071 (pattern : Twelve) : d259 (change pattern 7 8) = d1943 pattern := by
  change (if pattern.f then d241 (change pattern 7 8) else d240 (change pattern 7 8)) = d1943 pattern
  rw [s1070, s1066]
  rfl
theorem s1072 (pattern : Twelve) : d273 (change pattern 7 8) = d1944 pattern := by
  change (if pattern.e then d259 (change pattern 7 8) else d258 (change pattern 7 8)) = d1944 pattern
  rw [s1071, s1067]
  rfl
theorem s1073 (pattern : Twelve) : d284 (change pattern 7 8) = d1945 pattern := by
  change (if pattern.j then d273 (change pattern 7 8) else d272 (change pattern 7 8)) = d1945 pattern
  rw [s1072, s1063]
  rfl
theorem s1074 (pattern : Twelve) : d242 (change pattern 7 8) = d0 pattern := by
  change d0 (change pattern 7 8) = d0 pattern
  exact s1048 pattern
theorem s1075 (pattern : Twelve) : d243 (change pattern 7 8) = d1 pattern := by
  change d26 (change pattern 7 8) = d1 pattern
  exact s1051 pattern
theorem s1076 (pattern : Twelve) : d260 (change pattern 7 8) = d1859 pattern := by
  change (if pattern.f then d243 (change pattern 7 8) else d242 (change pattern 7 8)) = d1859 pattern
  rw [s1075, s1074]
  rfl
theorem s1077 (pattern : Twelve) : d244 (change pattern 7 8) = d0 pattern := by
  change d0 (change pattern 7 8) = d0 pattern
  exact s1048 pattern
theorem s1078 (pattern : Twelve) : d261 (change pattern 7 8) = d1946 pattern := by
  change (if pattern.f then d241 (change pattern 7 8) else d244 (change pattern 7 8)) = d1946 pattern
  rw [s1070, s1077]
  rfl
theorem s1079 (pattern : Twelve) : d274 (change pattern 7 8) = d1947 pattern := by
  change (if pattern.e then d261 (change pattern 7 8) else d260 (change pattern 7 8)) = d1947 pattern
  rw [s1078, s1076]
  rfl
theorem s1080 (pattern : Twelve) : d245 (change pattern 7 8) = d2 pattern := by
  change d30 (change pattern 7 8) = d2 pattern
  exact s1064 pattern
theorem s1081 (pattern : Twelve) : d246 (change pattern 7 8) = d2 pattern := by
  change d30 (change pattern 7 8) = d2 pattern
  exact s1064 pattern
theorem s1082 (pattern : Twelve) : d262 (change pattern 7 8) = d2 pattern := by
  change (if pattern.f then d246 (change pattern 7 8) else d245 (change pattern 7 8)) = d2 pattern
  rw [s1081, s1080]
  simp only [ite_self]
theorem s1083 (pattern : Twelve) : d263 (change pattern 7 8) = d1943 pattern := by
  change (if pattern.f then d241 (change pattern 7 8) else d246 (change pattern 7 8)) = d1943 pattern
  rw [s1070, s1081]
  rfl
theorem s1084 (pattern : Twelve) : d275 (change pattern 7 8) = d1944 pattern := by
  change (if pattern.e then d263 (change pattern 7 8) else d262 (change pattern 7 8)) = d1944 pattern
  rw [s1083, s1082]
  rfl
theorem s1085 (pattern : Twelve) : d285 (change pattern 7 8) = d1948 pattern := by
  change (if pattern.j then d275 (change pattern 7 8) else d274 (change pattern 7 8)) = d1948 pattern
  rw [s1084, s1079]
  rfl
theorem s1086 (pattern : Twelve) : d293 (change pattern 7 8) = d1949 pattern := by
  change (if pattern.d then d285 (change pattern 7 8) else d284 (change pattern 7 8)) = d1949 pattern
  rw [s1085, s1073]
  rfl
theorem s1087 (pattern : Twelve) : d247 (change pattern 7 8) = d2 pattern := by
  change d30 (change pattern 7 8) = d2 pattern
  exact s1064 pattern
theorem s1088 (pattern : Twelve) : d248 (change pattern 7 8) = d2 pattern := by
  change d30 (change pattern 7 8) = d2 pattern
  exact s1064 pattern
theorem s1089 (pattern : Twelve) : d264 (change pattern 7 8) = d2 pattern := by
  change (if pattern.f then d248 (change pattern 7 8) else d247 (change pattern 7 8)) = d2 pattern
  rw [s1088, s1087]
  simp only [ite_self]
theorem s1090 (pattern : Twelve) : d265 (change pattern 7 8) = d1943 pattern := by
  change (if pattern.f then d241 (change pattern 7 8) else d248 (change pattern 7 8)) = d1943 pattern
  rw [s1070, s1088]
  rfl
theorem s1091 (pattern : Twelve) : d276 (change pattern 7 8) = d1944 pattern := by
  change (if pattern.e then d265 (change pattern 7 8) else d264 (change pattern 7 8)) = d1944 pattern
  rw [s1090, s1089]
  rfl
theorem s1092 (pattern : Twelve) : d4 (change pattern 7 8) = d4 pattern := by
  rfl
theorem s1093 (pattern : Twelve) : d38 (change pattern 7 8) = d4 pattern := by
  change d4 (change pattern 7 8) = d4 pattern
  exact s1092 pattern
theorem s1094 (pattern : Twelve) : d249 (change pattern 7 8) = d4 pattern := by
  change d38 (change pattern 7 8) = d4 pattern
  exact s1093 pattern
theorem s1095 (pattern : Twelve) : d250 (change pattern 7 8) = d4 pattern := by
  change d38 (change pattern 7 8) = d4 pattern
  exact s1093 pattern
theorem s1096 (pattern : Twelve) : d266 (change pattern 7 8) = d4 pattern := by
  change (if pattern.f then d250 (change pattern 7 8) else d249 (change pattern 7 8)) = d4 pattern
  rw [s1095, s1094]
  simp only [ite_self]
theorem s1097 (pattern : Twelve) : d5 (change pattern 7 8) = d5 pattern := by
  rfl
theorem s1098 (pattern : Twelve) : d15 (change pattern 7 8) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 7 8) else d4 (change pattern 7 8)) = d15 pattern
  rw [s1097, s1092]
  rfl
theorem s1099 (pattern : Twelve) : d24 (change pattern 7 8) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 7 8) else d4 (change pattern 7 8)) = d24 pattern
  rw [s1098, s1092]
  rfl
theorem s1100 (pattern : Twelve) : d41 (change pattern 7 8) = d24 pattern := by
  change d24 (change pattern 7 8) = d24 pattern
  exact s1099 pattern
theorem s1101 (pattern : Twelve) : d251 (change pattern 7 8) = d24 pattern := by
  change d41 (change pattern 7 8) = d24 pattern
  exact s1100 pattern
theorem s1102 (pattern : Twelve) : d267 (change pattern 7 8) = d1950 pattern := by
  change (if pattern.f then d251 (change pattern 7 8) else d250 (change pattern 7 8)) = d1950 pattern
  rw [s1101, s1095]
  rfl
theorem s1103 (pattern : Twelve) : d277 (change pattern 7 8) = d1951 pattern := by
  change (if pattern.e then d267 (change pattern 7 8) else d266 (change pattern 7 8)) = d1951 pattern
  rw [s1102, s1096]
  rfl
theorem s1104 (pattern : Twelve) : d286 (change pattern 7 8) = d1952 pattern := by
  change (if pattern.j then d277 (change pattern 7 8) else d276 (change pattern 7 8)) = d1952 pattern
  rw [s1103, s1091]
  rfl
theorem s1105 (pattern : Twelve) : d252 (change pattern 7 8) = d2 pattern := by
  change d30 (change pattern 7 8) = d2 pattern
  exact s1064 pattern
theorem s1106 (pattern : Twelve) : d268 (change pattern 7 8) = d2 pattern := by
  change (if pattern.f then d246 (change pattern 7 8) else d252 (change pattern 7 8)) = d2 pattern
  rw [s1081, s1105]
  simp only [ite_self]
theorem s1107 (pattern : Twelve) : d278 (change pattern 7 8) = d1944 pattern := by
  change (if pattern.e then d263 (change pattern 7 8) else d268 (change pattern 7 8)) = d1944 pattern
  rw [s1083, s1106]
  rfl
theorem s1108 (pattern : Twelve) : d6 (change pattern 7 8) = d6 pattern := by
  rfl
theorem s1109 (pattern : Twelve) : d287 (change pattern 7 8) = d1953 pattern := by
  change (if pattern.j then d6 (change pattern 7 8) else d278 (change pattern 7 8)) = d1953 pattern
  rw [s1108, s1107]
  rfl
theorem s1110 (pattern : Twelve) : d294 (change pattern 7 8) = d1954 pattern := by
  change (if pattern.d then d287 (change pattern 7 8) else d286 (change pattern 7 8)) = d1954 pattern
  rw [s1109, s1104]
  rfl
theorem s1111 (pattern : Twelve) : d297 (change pattern 7 8) = d1955 pattern := by
  change (if pattern.c then d294 (change pattern 7 8) else d293 (change pattern 7 8)) = d1955 pattern
  rw [s1110, s1086]
  rfl
theorem s1112 (pattern : Twelve) : d253 (change pattern 7 8) = d0 pattern := by
  change d0 (change pattern 7 8) = d0 pattern
  exact s1048 pattern
theorem s1113 (pattern : Twelve) : d254 (change pattern 7 8) = d1 pattern := by
  change d26 (change pattern 7 8) = d1 pattern
  exact s1051 pattern
theorem s1114 (pattern : Twelve) : d269 (change pattern 7 8) = d1859 pattern := by
  change (if pattern.f then d254 (change pattern 7 8) else d253 (change pattern 7 8)) = d1859 pattern
  rw [s1113, s1112]
  rfl
theorem s1115 (pattern : Twelve) : d279 (change pattern 7 8) = d1956 pattern := by
  change (if pattern.e then d263 (change pattern 7 8) else d269 (change pattern 7 8)) = d1956 pattern
  rw [s1083, s1114]
  rfl
theorem s1116 (pattern : Twelve) : d280 (change pattern 7 8) = d1944 pattern := by
  change (if pattern.e then d263 (change pattern 7 8) else d246 (change pattern 7 8)) = d1944 pattern
  rw [s1083, s1081]
  rfl
theorem s1117 (pattern : Twelve) : d288 (change pattern 7 8) = d1957 pattern := by
  change (if pattern.j then d280 (change pattern 7 8) else d279 (change pattern 7 8)) = d1957 pattern
  rw [s1116, s1115]
  rfl
theorem s1118 (pattern : Twelve) : d281 (change pattern 7 8) = d1951 pattern := by
  change (if pattern.e then d267 (change pattern 7 8) else d250 (change pattern 7 8)) = d1951 pattern
  rw [s1102, s1095]
  rfl
theorem s1119 (pattern : Twelve) : d289 (change pattern 7 8) = d1952 pattern := by
  change (if pattern.j then d281 (change pattern 7 8) else d280 (change pattern 7 8)) = d1952 pattern
  rw [s1118, s1116]
  rfl
theorem s1120 (pattern : Twelve) : d290 (change pattern 7 8) = d1953 pattern := by
  change (if pattern.j then d6 (change pattern 7 8) else d280 (change pattern 7 8)) = d1953 pattern
  rw [s1108, s1116]
  rfl
theorem s1121 (pattern : Twelve) : d295 (change pattern 7 8) = d1954 pattern := by
  change (if pattern.d then d290 (change pattern 7 8) else d289 (change pattern 7 8)) = d1954 pattern
  rw [s1120, s1119]
  rfl
theorem s1122 (pattern : Twelve) : d298 (change pattern 7 8) = d1958 pattern := by
  change (if pattern.c then d295 (change pattern 7 8) else d288 (change pattern 7 8)) = d1958 pattern
  rw [s1121, s1117]
  rfl
theorem s1123 (pattern : Twelve) : d300 (change pattern 7 8) = d1959 pattern := by
  change (if pattern.g then d298 (change pattern 7 8) else d297 (change pattern 7 8)) = d1959 pattern
  rw [s1122, s1111]
  rfl
theorem s1124 (pattern : Twelve) : d255 (change pattern 7 8) = d18 pattern := by
  change d28 (change pattern 7 8) = d18 pattern
  exact s1060 pattern
theorem s1125 (pattern : Twelve) : d270 (change pattern 7 8) = d1941 pattern := by
  change (if pattern.f then d255 (change pattern 7 8) else d253 (change pattern 7 8)) = d1941 pattern
  rw [s1124, s1112]
  rfl
theorem s1126 (pattern : Twelve) : d282 (change pattern 7 8) = d1942 pattern := by
  change (if pattern.e then d270 (change pattern 7 8) else d269 (change pattern 7 8)) = d1942 pattern
  rw [s1125, s1114]
  rfl
theorem s1127 (pattern : Twelve) : d291 (change pattern 7 8) = d1945 pattern := by
  change (if pattern.j then d280 (change pattern 7 8) else d282 (change pattern 7 8)) = d1945 pattern
  rw [s1116, s1126]
  rfl
theorem s1128 (pattern : Twelve) : d271 (change pattern 7 8) = d1946 pattern := by
  change (if pattern.f then d241 (change pattern 7 8) else d253 (change pattern 7 8)) = d1946 pattern
  rw [s1070, s1112]
  rfl
theorem s1129 (pattern : Twelve) : d283 (change pattern 7 8) = d1947 pattern := by
  change (if pattern.e then d271 (change pattern 7 8) else d269 (change pattern 7 8)) = d1947 pattern
  rw [s1128, s1114]
  rfl
theorem s1130 (pattern : Twelve) : d292 (change pattern 7 8) = d1948 pattern := by
  change (if pattern.j then d280 (change pattern 7 8) else d283 (change pattern 7 8)) = d1948 pattern
  rw [s1116, s1129]
  rfl
theorem s1131 (pattern : Twelve) : d296 (change pattern 7 8) = d1949 pattern := by
  change (if pattern.d then d292 (change pattern 7 8) else d291 (change pattern 7 8)) = d1949 pattern
  rw [s1130, s1127]
  rfl
theorem s1132 (pattern : Twelve) : d299 (change pattern 7 8) = d1955 pattern := by
  change (if pattern.c then d295 (change pattern 7 8) else d296 (change pattern 7 8)) = d1955 pattern
  rw [s1121, s1131]
  rfl
theorem s1133 (pattern : Twelve) : d301 (change pattern 7 8) = d1959 pattern := by
  change (if pattern.g then d298 (change pattern 7 8) else d299 (change pattern 7 8)) = d1959 pattern
  rw [s1122, s1132]
  rfl
theorem s1134 (pattern : Twelve) : d302 (change pattern 7 8) = d1959 pattern := by
  change (if pattern.b then d301 (change pattern 7 8) else d300 (change pattern 7 8)) = d1959 pattern
  rw [s1133, s1123]
  simp only [ite_self]
theorem s1135 (pattern : Twelve) : d303 (change pattern 7 8) = d1959 pattern := by
  change (if pattern.a then d301 (change pattern 7 8) else d302 (change pattern 7 8)) = d1959 pattern
  rw [s1133, s1134]
  simp only [ite_self]
theorem s1136 (pattern : Twelve) : d27 (change pattern 7 8) = d1 pattern := by
  change d1 (change pattern 7 8) = d1 pattern
  exact s1050 pattern
theorem s1137 (pattern : Twelve) : d940 (change pattern 7 8) = d1 pattern := by
  change d27 (change pattern 7 8) = d1 pattern
  exact s1136 pattern
theorem s1138 (pattern : Twelve) : d947 (change pattern 7 8) = d1859 pattern := by
  change (if pattern.f then d940 (change pattern 7 8) else d237 (change pattern 7 8)) = d1859 pattern
  rw [s1137, s1054]
  rfl
theorem s1139 (pattern : Twelve) : d7 (change pattern 7 8) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 7 8) else d0 (change pattern 7 8)) = d7 pattern
  rw [s1050, s1048]
  rfl
theorem s1140 (pattern : Twelve) : d17 (change pattern 7 8) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 7 8) else d0 (change pattern 7 8)) = d17 pattern
  rw [s1139, s1048]
  rfl
theorem s1141 (pattern : Twelve) : d941 (change pattern 7 8) = d17 pattern := by
  change d17 (change pattern 7 8) = d17 pattern
  exact s1140 pattern
theorem s1142 (pattern : Twelve) : d16 (change pattern 7 8) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 7 8) else d2 (change pattern 7 8)) = d16 pattern
  rw [s1092, s1055]
  rfl
theorem s1143 (pattern : Twelve) : d12 (change pattern 7 8) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 7 8) else d3 (change pattern 7 8)) = d12 pattern
  rw [s1097, s1057]
  rfl
theorem s1144 (pattern : Twelve) : d25 (change pattern 7 8) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 7 8) else d16 (change pattern 7 8)) = d25 pattern
  rw [s1143, s1142]
  rfl
theorem s1145 (pattern : Twelve) : d817 (change pattern 7 8) = d25 pattern := by
  change d25 (change pattern 7 8) = d25 pattern
  exact s1144 pattern
theorem s1146 (pattern : Twelve) : d942 (change pattern 7 8) = d25 pattern := by
  change d817 (change pattern 7 8) = d25 pattern
  exact s1145 pattern
theorem s1147 (pattern : Twelve) : d948 (change pattern 7 8) = d1960 pattern := by
  change (if pattern.f then d942 (change pattern 7 8) else d941 (change pattern 7 8)) = d1960 pattern
  rw [s1146, s1141]
  rfl
theorem s1148 (pattern : Twelve) : d955 (change pattern 7 8) = d1961 pattern := by
  change (if pattern.e then d948 (change pattern 7 8) else d947 (change pattern 7 8)) = d1961 pattern
  rw [s1147, s1138]
  rfl
theorem s1149 (pattern : Twelve) : d949 (change pattern 7 8) = d1962 pattern := by
  change (if pattern.f then d942 (change pattern 7 8) else d241 (change pattern 7 8)) = d1962 pattern
  rw [s1146, s1070]
  rfl
theorem s1150 (pattern : Twelve) : d956 (change pattern 7 8) = d1963 pattern := by
  change (if pattern.e then d949 (change pattern 7 8) else d259 (change pattern 7 8)) = d1963 pattern
  rw [s1149, s1071]
  rfl
theorem s1151 (pattern : Twelve) : d963 (change pattern 7 8) = d1964 pattern := by
  change (if pattern.j then d956 (change pattern 7 8) else d955 (change pattern 7 8)) = d1964 pattern
  rw [s1150, s1148]
  rfl
theorem s1152 (pattern : Twelve) : d943 (change pattern 7 8) = d1 pattern := by
  change d27 (change pattern 7 8) = d1 pattern
  exact s1136 pattern
theorem s1153 (pattern : Twelve) : d950 (change pattern 7 8) = d1859 pattern := by
  change (if pattern.f then d943 (change pattern 7 8) else d244 (change pattern 7 8)) = d1859 pattern
  rw [s1152, s1077]
  rfl
theorem s1154 (pattern : Twelve) : d944 (change pattern 7 8) = d17 pattern := by
  change d17 (change pattern 7 8) = d17 pattern
  exact s1140 pattern
theorem s1155 (pattern : Twelve) : d951 (change pattern 7 8) = d1960 pattern := by
  change (if pattern.f then d942 (change pattern 7 8) else d944 (change pattern 7 8)) = d1960 pattern
  rw [s1146, s1154]
  rfl
theorem s1156 (pattern : Twelve) : d957 (change pattern 7 8) = d1961 pattern := by
  change (if pattern.e then d951 (change pattern 7 8) else d950 (change pattern 7 8)) = d1961 pattern
  rw [s1155, s1153]
  rfl
theorem s1157 (pattern : Twelve) : d958 (change pattern 7 8) = d1963 pattern := by
  change (if pattern.e then d949 (change pattern 7 8) else d263 (change pattern 7 8)) = d1963 pattern
  rw [s1149, s1083]
  rfl
theorem s1158 (pattern : Twelve) : d964 (change pattern 7 8) = d1964 pattern := by
  change (if pattern.j then d958 (change pattern 7 8) else d957 (change pattern 7 8)) = d1964 pattern
  rw [s1157, s1156]
  rfl
theorem s1159 (pattern : Twelve) : d970 (change pattern 7 8) = d1964 pattern := by
  change (if pattern.d then d964 (change pattern 7 8) else d963 (change pattern 7 8)) = d1964 pattern
  rw [s1158, s1151]
  simp only [ite_self]
theorem s1160 (pattern : Twelve) : d959 (change pattern 7 8) = d1963 pattern := by
  change (if pattern.e then d949 (change pattern 7 8) else d265 (change pattern 7 8)) = d1963 pattern
  rw [s1149, s1090]
  rfl
theorem s1161 (pattern : Twelve) : d13 (change pattern 7 8) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 7 8) else d4 (change pattern 7 8)) = d13 pattern
  rw [s1108, s1092]
  rfl
theorem s1162 (pattern : Twelve) : d14 (change pattern 7 8) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 7 8) else d5 (change pattern 7 8)) = d14 pattern
  rw [s1108, s1097]
  rfl
theorem s1163 (pattern : Twelve) : d21 (change pattern 7 8) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 7 8) else d13 (change pattern 7 8)) = d21 pattern
  rw [s1162, s1161]
  rfl
theorem s1164 (pattern : Twelve) : d821 (change pattern 7 8) = d21 pattern := by
  change d21 (change pattern 7 8) = d21 pattern
  exact s1163 pattern
theorem s1165 (pattern : Twelve) : d945 (change pattern 7 8) = d21 pattern := by
  change d821 (change pattern 7 8) = d21 pattern
  exact s1164 pattern
theorem s1166 (pattern : Twelve) : d952 (change pattern 7 8) = d1965 pattern := by
  change (if pattern.f then d945 (change pattern 7 8) else d251 (change pattern 7 8)) = d1965 pattern
  rw [s1165, s1101]
  rfl
theorem s1167 (pattern : Twelve) : d960 (change pattern 7 8) = d1966 pattern := by
  change (if pattern.e then d952 (change pattern 7 8) else d267 (change pattern 7 8)) = d1966 pattern
  rw [s1166, s1102]
  rfl
theorem s1168 (pattern : Twelve) : d965 (change pattern 7 8) = d1967 pattern := by
  change (if pattern.j then d960 (change pattern 7 8) else d959 (change pattern 7 8)) = d1967 pattern
  rw [s1167, s1160]
  rfl
theorem s1169 (pattern : Twelve) : d966 (change pattern 7 8) = d1968 pattern := by
  change (if pattern.j then d6 (change pattern 7 8) else d958 (change pattern 7 8)) = d1968 pattern
  rw [s1108, s1157]
  rfl
theorem s1170 (pattern : Twelve) : d971 (change pattern 7 8) = d1969 pattern := by
  change (if pattern.d then d966 (change pattern 7 8) else d965 (change pattern 7 8)) = d1969 pattern
  rw [s1169, s1168]
  rfl
theorem s1171 (pattern : Twelve) : d973 (change pattern 7 8) = d1970 pattern := by
  change (if pattern.c then d971 (change pattern 7 8) else d970 (change pattern 7 8)) = d1970 pattern
  rw [s1170, s1159]
  rfl
theorem s1172 (pattern : Twelve) : d953 (change pattern 7 8) = d1859 pattern := by
  change (if pattern.f then d943 (change pattern 7 8) else d253 (change pattern 7 8)) = d1859 pattern
  rw [s1152, s1112]
  rfl
theorem s1173 (pattern : Twelve) : d823 (change pattern 7 8) = d2 pattern := by
  change d2 (change pattern 7 8) = d2 pattern
  exact s1055 pattern
theorem s1174 (pattern : Twelve) : d946 (change pattern 7 8) = d2 pattern := by
  change d823 (change pattern 7 8) = d2 pattern
  exact s1173 pattern
theorem s1175 (pattern : Twelve) : d954 (change pattern 7 8) = d1971 pattern := by
  change (if pattern.f then d942 (change pattern 7 8) else d946 (change pattern 7 8)) = d1971 pattern
  rw [s1146, s1174]
  rfl
theorem s1176 (pattern : Twelve) : d961 (change pattern 7 8) = d1972 pattern := by
  change (if pattern.e then d954 (change pattern 7 8) else d953 (change pattern 7 8)) = d1972 pattern
  rw [s1175, s1172]
  rfl
theorem s1177 (pattern : Twelve) : d967 (change pattern 7 8) = d1973 pattern := by
  change (if pattern.j then d958 (change pattern 7 8) else d961 (change pattern 7 8)) = d1973 pattern
  rw [s1157, s1176]
  rfl
theorem s1178 (pattern : Twelve) : d968 (change pattern 7 8) = d1967 pattern := by
  change (if pattern.j then d960 (change pattern 7 8) else d958 (change pattern 7 8)) = d1967 pattern
  rw [s1167, s1157]
  rfl
theorem s1179 (pattern : Twelve) : d972 (change pattern 7 8) = d1969 pattern := by
  change (if pattern.d then d966 (change pattern 7 8) else d968 (change pattern 7 8)) = d1969 pattern
  rw [s1169, s1178]
  rfl
theorem s1180 (pattern : Twelve) : d974 (change pattern 7 8) = d1974 pattern := by
  change (if pattern.c then d972 (change pattern 7 8) else d967 (change pattern 7 8)) = d1974 pattern
  rw [s1179, s1177]
  rfl
theorem s1181 (pattern : Twelve) : d976 (change pattern 7 8) = d1975 pattern := by
  change (if pattern.g then d974 (change pattern 7 8) else d973 (change pattern 7 8)) = d1975 pattern
  rw [s1180, s1171]
  rfl
theorem s1182 (pattern : Twelve) : d962 (change pattern 7 8) = d1961 pattern := by
  change (if pattern.e then d951 (change pattern 7 8) else d953 (change pattern 7 8)) = d1961 pattern
  rw [s1155, s1172]
  rfl
theorem s1183 (pattern : Twelve) : d969 (change pattern 7 8) = d1964 pattern := by
  change (if pattern.j then d958 (change pattern 7 8) else d962 (change pattern 7 8)) = d1964 pattern
  rw [s1157, s1182]
  rfl
theorem s1184 (pattern : Twelve) : d975 (change pattern 7 8) = d1970 pattern := by
  change (if pattern.c then d972 (change pattern 7 8) else d969 (change pattern 7 8)) = d1970 pattern
  rw [s1179, s1183]
  rfl
theorem s1185 (pattern : Twelve) : d977 (change pattern 7 8) = d1975 pattern := by
  change (if pattern.g then d974 (change pattern 7 8) else d975 (change pattern 7 8)) = d1975 pattern
  rw [s1180, s1184]
  rfl
theorem s1186 (pattern : Twelve) : d978 (change pattern 7 8) = d1975 pattern := by
  change (if pattern.b then d977 (change pattern 7 8) else d976 (change pattern 7 8)) = d1975 pattern
  rw [s1185, s1181]
  simp only [ite_self]
theorem s1187 (pattern : Twelve) : d979 (change pattern 7 8) = d1975 pattern := by
  change (if pattern.a then d977 (change pattern 7 8) else d978 (change pattern 7 8)) = d1975 pattern
  rw [s1185, s1186]
  simp only [ite_self]
theorem s1188 (pattern : Twelve) : d872 (change pattern 7 8) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 7 8) else d1 (change pattern 7 8)) = d872 pattern
  rw [s1056, s1050]
  rfl
theorem s1189 (pattern : Twelve) : d1278 (change pattern 7 8) = d872 pattern := by
  change d872 (change pattern 7 8) = d872 pattern
  exact s1188 pattern
theorem s1190 (pattern : Twelve) : d1380 (change pattern 7 8) = d872 pattern := by
  change d1278 (change pattern 7 8) = d872 pattern
  exact s1189 pattern
theorem s1191 (pattern : Twelve) : d1385 (change pattern 7 8) = d1976 pattern := by
  change (if pattern.f then d1380 (change pattern 7 8) else d941 (change pattern 7 8)) = d1976 pattern
  rw [s1190, s1141]
  rfl
theorem s1192 (pattern : Twelve) : d10 (change pattern 7 8) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 7 8) else d0 (change pattern 7 8)) = d10 pattern
  rw [s1055, s1048]
  rfl
theorem s1193 (pattern : Twelve) : d11 (change pattern 7 8) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 7 8) else d1 (change pattern 7 8)) = d11 pattern
  rw [s1057, s1050]
  rfl
theorem s1194 (pattern : Twelve) : d19 (change pattern 7 8) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 7 8) else d10 (change pattern 7 8)) = d19 pattern
  rw [s1193, s1192]
  rfl
theorem s1195 (pattern : Twelve) : d1381 (change pattern 7 8) = d19 pattern := by
  change d19 (change pattern 7 8) = d19 pattern
  exact s1194 pattern
theorem s1196 (pattern : Twelve) : d1386 (change pattern 7 8) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 7 8) else d1381 (change pattern 7 8)) = d1294 pattern
  rw [s1108, s1195]
  rfl
theorem s1197 (pattern : Twelve) : d1393 (change pattern 7 8) = d1977 pattern := by
  change (if pattern.e then d1386 (change pattern 7 8) else d1385 (change pattern 7 8)) = d1977 pattern
  rw [s1196, s1191]
  rfl
theorem s1198 (pattern : Twelve) : d117 (change pattern 7 8) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 7 8) else d3 (change pattern 7 8)) = d117 pattern
  rw [s1092, s1057]
  rfl
theorem s1199 (pattern : Twelve) : d1276 (change pattern 7 8) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 7 8) else d9 (change pattern 7 8)) = d1276 pattern
  rw [s1198, s1058]
  rfl
end NetHack.Sokoban21.Diagram
