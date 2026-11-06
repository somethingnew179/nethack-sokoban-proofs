/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions50
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub6120 (p : Pattern) : d1040 (change p 162 (some 161)) = d4829 p := by
  change (if p 115 then d1039 (change p 162 (some 161)) else d1031 (change p 162 (some 161))) = d4829 p
  rw [sub6119, sub6111]
  rfl
theorem sub6121 (p : Pattern) : d1041 (change p 162 (some 161)) = d4829 p := by
  change (if p 71 then d1040 (change p 162 (some 161)) else d1014 (change p 162 (some 161))) = d4829 p
  rw [sub6120, sub6098]
  simp only [ite_self]
theorem sub6122 (p : Pattern) : d1 (change p 162 (some 161)) = d1 p := by
  rfl
theorem sub6123 (p : Pattern) : d102 (change p 162 (some 161)) = d102 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d1 (change p 162 (some 161))) = d102 p
  rw [sub6009, sub6122]
  rfl
theorem sub6124 (p : Pattern) : d103 (change p 162 (some 161)) = d103 p := by
  change (if p 246 then d102 (change p 162 (some 161)) else d1 (change p 162 (some 161))) = d103 p
  rw [sub6123, sub6122]
  rfl
theorem sub6125 (p : Pattern) : d104 (change p 162 (some 161)) = d104 p := by
  change (if p 204 then d12 (change p 162 (some 161)) else d103 (change p 162 (some 161))) = d104 p
  rw [sub6009, sub6124]
  rfl
theorem sub6126 (p : Pattern) : d105 (change p 162 (some 161)) = d105 p := by
  change (if p 182 then d104 (change p 162 (some 161)) else d103 (change p 162 (some 161))) = d105 p
  rw [sub6125, sub6124]
  rfl
theorem sub6127 (p : Pattern) : d3 (change p 162 (some 161)) = d3 p := by
  rfl
theorem sub6128 (p : Pattern) : d115 (change p 162 (some 161)) = d115 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d3 (change p 162 (some 161))) = d115 p
  rw [sub6009, sub6127]
  rfl
theorem sub6129 (p : Pattern) : d116 (change p 162 (some 161)) = d116 p := by
  change (if p 246 then d115 (change p 162 (some 161)) else d3 (change p 162 (some 161))) = d116 p
  rw [sub6128, sub6127]
  rfl
theorem sub6130 (p : Pattern) : d117 (change p 162 (some 161)) = d117 p := by
  change (if p 204 then d12 (change p 162 (some 161)) else d116 (change p 162 (some 161))) = d117 p
  rw [sub6009, sub6129]
  rfl
theorem sub6131 (p : Pattern) : d118 (change p 162 (some 161)) = d118 p := by
  change (if p 182 then d117 (change p 162 (some 161)) else d103 (change p 162 (some 161))) = d118 p
  rw [sub6130, sub6124]
  rfl
theorem sub6132 (p : Pattern) : d1043 (change p 162 (some 161)) = d1043 p := by
  change (if p 163 then d118 (change p 162 (some 161)) else d105 (change p 162 (some 161))) = d1043 p
  rw [sub6131, sub6126]
  rfl
theorem sub6133 (p : Pattern) : d1044 (change p 162 (some 161)) = d1043 p := by
  change d1043 (change p 162 (some 161)) = d1043 p
  exact sub6132 p
theorem sub6134 (p : Pattern) : d1045 (change p 162 (some 161)) = d1043 p := by
  change d1044 (change p 162 (some 161)) = d1043 p
  exact sub6133 p
theorem sub6135 (p : Pattern) : d124 (change p 162 (some 161)) = d124 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d103 (change p 162 (some 161))) = d124 p
  rw [sub6009, sub6124]
  rfl
theorem sub6136 (p : Pattern) : d5 (change p 162 (some 161)) = d5 p := by
  rfl
theorem sub6137 (p : Pattern) : d106 (change p 162 (some 161)) = d106 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d5 (change p 162 (some 161))) = d106 p
  rw [sub6009, sub6136]
  rfl
theorem sub6138 (p : Pattern) : d107 (change p 162 (some 161)) = d107 p := by
  change (if p 246 then d106 (change p 162 (some 161)) else d5 (change p 162 (some 161))) = d107 p
  rw [sub6137, sub6136]
  rfl
theorem sub6139 (p : Pattern) : d125 (change p 162 (some 161)) = d125 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d107 (change p 162 (some 161))) = d125 p
  rw [sub6009, sub6138]
  rfl
theorem sub6140 (p : Pattern) : d126 (change p 162 (some 161)) = d126 p := by
  change (if p 163 then d125 (change p 162 (some 161)) else d124 (change p 162 (some 161))) = d126 p
  rw [sub6139, sub6135]
  rfl
theorem sub6141 (p : Pattern) : d1047 (change p 162 (some 161)) = d126 p := by
  change d126 (change p 162 (some 161)) = d126 p
  exact sub6140 p
theorem sub6142 (p : Pattern) : d1048 (change p 162 (some 161)) = d126 p := by
  change d1047 (change p 162 (some 161)) = d126 p
  exact sub6141 p
theorem sub6143 (p : Pattern) : d1049 (change p 162 (some 161)) = d4830 p := by
  change (if p 160 then d1048 (change p 162 (some 161)) else d1045 (change p 162 (some 161))) = d4830 p
  rw [sub6142, sub6134]
  rfl
theorem sub6144 (p : Pattern) : d132 (change p 162 (some 161)) = d132 p := by
  change (if p 182 then d117 (change p 162 (some 161)) else d116 (change p 162 (some 161))) = d132 p
  rw [sub6130, sub6129]
  rfl
theorem sub6145 (p : Pattern) : d108 (change p 162 (some 161)) = d108 p := by
  change (if p 204 then d12 (change p 162 (some 161)) else d107 (change p 162 (some 161))) = d108 p
  rw [sub6009, sub6138]
  rfl
theorem sub6146 (p : Pattern) : d861 (change p 162 (some 161)) = d861 p := by
  change (if p 182 then d108 (change p 162 (some 161)) else d116 (change p 162 (some 161))) = d861 p
  rw [sub6145, sub6129]
  rfl
theorem sub6147 (p : Pattern) : d862 (change p 162 (some 161)) = d862 p := by
  change (if p 163 then d861 (change p 162 (some 161)) else d132 (change p 162 (some 161))) = d862 p
  rw [sub6146, sub6144]
  rfl
theorem sub6148 (p : Pattern) : d1051 (change p 162 (some 161)) = d862 p := by
  change d862 (change p 162 (some 161)) = d862 p
  exact sub6147 p
theorem sub6149 (p : Pattern) : d1052 (change p 162 (some 161)) = d862 p := by
  change d1051 (change p 162 (some 161)) = d862 p
  exact sub6148 p
theorem sub6150 (p : Pattern) : d139 (change p 162 (some 161)) = d139 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d116 (change p 162 (some 161))) = d139 p
  rw [sub6009, sub6129]
  rfl
theorem sub6151 (p : Pattern) : d7 (change p 162 (some 161)) = d7 p := by
  rfl
theorem sub6152 (p : Pattern) : d119 (change p 162 (some 161)) = d119 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d7 (change p 162 (some 161))) = d119 p
  rw [sub6009, sub6151]
  rfl
theorem sub6153 (p : Pattern) : d120 (change p 162 (some 161)) = d120 p := by
  change (if p 246 then d119 (change p 162 (some 161)) else d7 (change p 162 (some 161))) = d120 p
  rw [sub6152, sub6151]
  rfl
theorem sub6154 (p : Pattern) : d229 (change p 162 (some 161)) = d229 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d120 (change p 162 (some 161))) = d229 p
  rw [sub6009, sub6153]
  rfl
theorem sub6155 (p : Pattern) : d1053 (change p 162 (some 161)) = d1053 p := by
  change (if p 163 then d229 (change p 162 (some 161)) else d139 (change p 162 (some 161))) = d1053 p
  rw [sub6154, sub6150]
  rfl
theorem sub6156 (p : Pattern) : d1054 (change p 162 (some 161)) = d1053 p := by
  change d1053 (change p 162 (some 161)) = d1053 p
  exact sub6155 p
theorem sub6157 (p : Pattern) : d1055 (change p 162 (some 161)) = d1053 p := by
  change d1054 (change p 162 (some 161)) = d1053 p
  exact sub6156 p
theorem sub6158 (p : Pattern) : d1056 (change p 162 (some 161)) = d4831 p := by
  change (if p 160 then d1055 (change p 162 (some 161)) else d1052 (change p 162 (some 161))) = d4831 p
  rw [sub6157, sub6149]
  rfl
theorem sub6159 (p : Pattern) : d1057 (change p 162 (some 161)) = d4832 p := by
  change (if p 141 then d1056 (change p 162 (some 161)) else d1049 (change p 162 (some 161))) = d4832 p
  rw [sub6158, sub6143]
  rfl
theorem sub6160 (p : Pattern) : d133 (change p 162 (some 161)) = d133 p := by
  change (if p 163 then d132 (change p 162 (some 161)) else d105 (change p 162 (some 161))) = d133 p
  rw [sub6144, sub6126]
  rfl
theorem sub6161 (p : Pattern) : d1059 (change p 162 (some 161)) = d133 p := by
  change d133 (change p 162 (some 161)) = d133 p
  exact sub6160 p
theorem sub6162 (p : Pattern) : d1060 (change p 162 (some 161)) = d133 p := by
  change d1059 (change p 162 (some 161)) = d133 p
  exact sub6161 p
theorem sub6163 (p : Pattern) : d1062 (change p 162 (some 161)) = d12 p := by
  change d12 (change p 162 (some 161)) = d12 p
  exact sub6009 p
theorem sub6164 (p : Pattern) : d1063 (change p 162 (some 161)) = d4833 p := by
  change (if p 160 then d1062 (change p 162 (some 161)) else d1060 (change p 162 (some 161))) = d4833 p
  rw [sub6163, sub6162]
  rfl
theorem sub6165 (p : Pattern) : d109 (change p 162 (some 161)) = d109 p := by
  change (if p 182 then d108 (change p 162 (some 161)) else d107 (change p 162 (some 161))) = d109 p
  rw [sub6145, sub6138]
  rfl
theorem sub6166 (p : Pattern) : d873 (change p 162 (some 161)) = d873 p := by
  change (if p 163 then d109 (change p 162 (some 161)) else d132 (change p 162 (some 161))) = d873 p
  rw [sub6165, sub6144]
  rfl
theorem sub6167 (p : Pattern) : d1064 (change p 162 (some 161)) = d873 p := by
  change d873 (change p 162 (some 161)) = d873 p
  exact sub6166 p
theorem sub6168 (p : Pattern) : d1065 (change p 162 (some 161)) = d873 p := by
  change d1064 (change p 162 (some 161)) = d873 p
  exact sub6167 p
theorem sub6169 (p : Pattern) : d1066 (change p 162 (some 161)) = d12 p := by
  change d12 (change p 162 (some 161)) = d12 p
  exact sub6009 p
theorem sub6170 (p : Pattern) : d1067 (change p 162 (some 161)) = d4834 p := by
  change (if p 160 then d1066 (change p 162 (some 161)) else d1065 (change p 162 (some 161))) = d4834 p
  rw [sub6169, sub6168]
  rfl
theorem sub6171 (p : Pattern) : d1068 (change p 162 (some 161)) = d4835 p := by
  change (if p 141 then d1067 (change p 162 (some 161)) else d1063 (change p 162 (some 161))) = d4835 p
  rw [sub6170, sub6164]
  rfl
theorem sub6172 (p : Pattern) : d1069 (change p 162 (some 161)) = d4836 p := by
  change (if p 138 then d1068 (change p 162 (some 161)) else d1057 (change p 162 (some 161))) = d4836 p
  rw [sub6171, sub6159]
  rfl
theorem sub6173 (p : Pattern) : d1071 (change p 162 (some 161)) = d133 p := by
  change d1059 (change p 162 (some 161)) = d133 p
  exact sub6161 p
theorem sub6174 (p : Pattern) : d1072 (change p 162 (some 161)) = d4833 p := by
  change (if p 160 then d1062 (change p 162 (some 161)) else d1071 (change p 162 (some 161))) = d4833 p
  rw [sub6163, sub6173]
  rfl
theorem sub6175 (p : Pattern) : d1074 (change p 162 (some 161)) = d873 p := by
  change d1064 (change p 162 (some 161)) = d873 p
  exact sub6167 p
theorem sub6176 (p : Pattern) : d1075 (change p 162 (some 161)) = d4834 p := by
  change (if p 160 then d1066 (change p 162 (some 161)) else d1074 (change p 162 (some 161))) = d4834 p
  rw [sub6169, sub6175]
  rfl
theorem sub6177 (p : Pattern) : d1076 (change p 162 (some 161)) = d4835 p := by
  change (if p 141 then d1075 (change p 162 (some 161)) else d1072 (change p 162 (some 161))) = d4835 p
  rw [sub6176, sub6174]
  rfl
theorem sub6178 (p : Pattern) : d160 (change p 162 (some 161)) = d12 p := by
  change d12 (change p 162 (some 161)) = d12 p
  exact sub6009 p
theorem sub6179 (p : Pattern) : d161 (change p 162 (some 161)) = d12 p := by
  change (if p 160 then d12 (change p 162 (some 161)) else d160 (change p 162 (some 161))) = d12 p
  rw [sub6009, sub6178]
  simp only [ite_self]
theorem sub6180 (p : Pattern) : d162 (change p 162 (some 161)) = d12 p := by
  change (if p 141 then d12 (change p 162 (some 161)) else d161 (change p 162 (some 161))) = d12 p
  rw [sub6009, sub6179]
  simp only [ite_self]
theorem sub6181 (p : Pattern) : d1077 (change p 162 (some 161)) = d4837 p := by
  change (if p 138 then d162 (change p 162 (some 161)) else d1076 (change p 162 (some 161))) = d4837 p
  rw [sub6180, sub6177]
  rfl
theorem sub6182 (p : Pattern) : d1078 (change p 162 (some 161)) = d4838 p := by
  change (if p 116 then d1077 (change p 162 (some 161)) else d1069 (change p 162 (some 161))) = d4838 p
  rw [sub6181, sub6172]
  rfl
theorem sub6183 (p : Pattern) : d1080 (change p 162 (some 161)) = d1043 p := by
  change d1043 (change p 162 (some 161)) = d1043 p
  exact sub6132 p
theorem sub6184 (p : Pattern) : d1081 (change p 162 (some 161)) = d1043 p := by
  change d1080 (change p 162 (some 161)) = d1043 p
  exact sub6183 p
theorem sub6185 (p : Pattern) : d1083 (change p 162 (some 161)) = d126 p := by
  change d1047 (change p 162 (some 161)) = d126 p
  exact sub6141 p
theorem sub6186 (p : Pattern) : d1084 (change p 162 (some 161)) = d4830 p := by
  change (if p 160 then d1083 (change p 162 (some 161)) else d1081 (change p 162 (some 161))) = d4830 p
  rw [sub6185, sub6184]
  rfl
theorem sub6187 (p : Pattern) : d1086 (change p 162 (some 161)) = d862 p := by
  change d1051 (change p 162 (some 161)) = d862 p
  exact sub6148 p
theorem sub6188 (p : Pattern) : d1087 (change p 162 (some 161)) = d4831 p := by
  change (if p 160 then d1055 (change p 162 (some 161)) else d1086 (change p 162 (some 161))) = d4831 p
  rw [sub6157, sub6187]
  rfl
theorem sub6189 (p : Pattern) : d1088 (change p 162 (some 161)) = d4832 p := by
  change (if p 141 then d1087 (change p 162 (some 161)) else d1084 (change p 162 (some 161))) = d4832 p
  rw [sub6188, sub6186]
  rfl
theorem sub6190 (p : Pattern) : d1090 (change p 162 (some 161)) = d133 p := by
  change d1059 (change p 162 (some 161)) = d133 p
  exact sub6161 p
theorem sub6191 (p : Pattern) : d1091 (change p 162 (some 161)) = d4833 p := by
  change (if p 160 then d1062 (change p 162 (some 161)) else d1090 (change p 162 (some 161))) = d4833 p
  rw [sub6163, sub6190]
  rfl
theorem sub6192 (p : Pattern) : d1092 (change p 162 (some 161)) = d4835 p := by
  change (if p 141 then d1067 (change p 162 (some 161)) else d1091 (change p 162 (some 161))) = d4835 p
  rw [sub6170, sub6191]
  rfl
theorem sub6193 (p : Pattern) : d1093 (change p 162 (some 161)) = d4836 p := by
  change (if p 138 then d1092 (change p 162 (some 161)) else d1088 (change p 162 (some 161))) = d4836 p
  rw [sub6192, sub6189]
  rfl
theorem sub6194 (p : Pattern) : d1094 (change p 162 (some 161)) = d4837 p := by
  change (if p 138 then d12 (change p 162 (some 161)) else d1092 (change p 162 (some 161))) = d4837 p
  rw [sub6009, sub6192]
  rfl
theorem sub6195 (p : Pattern) : d1095 (change p 162 (some 161)) = d4838 p := by
  change (if p 116 then d1094 (change p 162 (some 161)) else d1093 (change p 162 (some 161))) = d4838 p
  rw [sub6194, sub6193]
  rfl
theorem sub6196 (p : Pattern) : d1096 (change p 162 (some 161)) = d4838 p := by
  change (if p 115 then d1095 (change p 162 (some 161)) else d1078 (change p 162 (some 161))) = d4838 p
  rw [sub6195, sub6182]
  simp only [ite_self]
theorem sub6197 (p : Pattern) : d1097 (change p 162 (some 161)) = d4839 p := by
  change (if p 71 then d1096 (change p 162 (some 161)) else d1014 (change p 162 (some 161))) = d4839 p
  rw [sub6196, sub6098]
  rfl
theorem sub6198 (p : Pattern) : d1098 (change p 162 (some 161)) = d4840 p := by
  change (if p 49 then d1097 (change p 162 (some 161)) else d1041 (change p 162 (some 161))) = d4840 p
  rw [sub6197, sub6121]
  rfl
theorem sub6199 (p : Pattern) : d1099 (change p 162 (some 161)) = d808 p := by
  change d972 (change p 162 (some 161)) = d808 p
  exact sub6054 p
theorem sub6200 (p : Pattern) : d1101 (change p 162 (some 161)) = d12 p := by
  change d12 (change p 162 (some 161)) = d12 p
  exact sub6009 p
theorem sub6201 (p : Pattern) : d1102 (change p 162 (some 161)) = d4822 p := by
  change (if p 160 then d1101 (change p 162 (some 161)) else d1099 (change p 162 (some 161))) = d4822 p
  rw [sub6200, sub6199]
  rfl
theorem sub6202 (p : Pattern) : d1103 (change p 162 (some 161)) = d4823 p := by
  change (if p 141 then d1102 (change p 162 (some 161)) else d1003 (change p 162 (some 161))) = d4823 p
  rw [sub6201, sub6088]
  rfl
theorem sub6203 (p : Pattern) : d1104 (change p 162 (some 161)) = d4824 p := by
  change (if p 138 then d1103 (change p 162 (some 161)) else d1036 (change p 162 (some 161))) = d4824 p
  rw [sub6202, sub6116]
  rfl
theorem sub6204 (p : Pattern) : d1105 (change p 162 (some 161)) = d4827 p := by
  change (if p 138 then d12 (change p 162 (some 161)) else d1103 (change p 162 (some 161))) = d4827 p
  rw [sub6009, sub6202]
  rfl
theorem sub6205 (p : Pattern) : d1106 (change p 162 (some 161)) = d4828 p := by
  change (if p 116 then d1105 (change p 162 (some 161)) else d1104 (change p 162 (some 161))) = d4828 p
  rw [sub6204, sub6203]
  rfl
theorem sub6206 (p : Pattern) : d1107 (change p 162 (some 161)) = d4829 p := by
  change (if p 115 then d1106 (change p 162 (some 161)) else d1031 (change p 162 (some 161))) = d4829 p
  rw [sub6205, sub6111]
  rfl
theorem sub6207 (p : Pattern) : d1108 (change p 162 (some 161)) = d4829 p := by
  change (if p 71 then d1107 (change p 162 (some 161)) else d1014 (change p 162 (some 161))) = d4829 p
  rw [sub6206, sub6098]
  simp only [ite_self]
theorem sub6208 (p : Pattern) : d1110 (change p 162 (some 161)) = d862 p := by
  change d1051 (change p 162 (some 161)) = d862 p
  exact sub6148 p
theorem sub6209 (p : Pattern) : d1111 (change p 162 (some 161)) = d4831 p := by
  change (if p 160 then d1055 (change p 162 (some 161)) else d1110 (change p 162 (some 161))) = d4831 p
  rw [sub6157, sub6208]
  rfl
theorem sub6210 (p : Pattern) : d1112 (change p 162 (some 161)) = d4832 p := by
  change (if p 141 then d1111 (change p 162 (some 161)) else d1049 (change p 162 (some 161))) = d4832 p
  rw [sub6209, sub6143]
  rfl
theorem sub6211 (p : Pattern) : d1113 (change p 162 (some 161)) = d4836 p := by
  change (if p 138 then d1068 (change p 162 (some 161)) else d1112 (change p 162 (some 161))) = d4836 p
  rw [sub6171, sub6210]
  rfl
theorem sub6212 (p : Pattern) : d1114 (change p 162 (some 161)) = d4835 p := by
  change (if p 141 then d1067 (change p 162 (some 161)) else d1072 (change p 162 (some 161))) = d4835 p
  rw [sub6170, sub6174]
  rfl
theorem sub6213 (p : Pattern) : d1115 (change p 162 (some 161)) = d4837 p := by
  change (if p 138 then d162 (change p 162 (some 161)) else d1114 (change p 162 (some 161))) = d4837 p
  rw [sub6180, sub6212]
  rfl
theorem sub6214 (p : Pattern) : d1116 (change p 162 (some 161)) = d4838 p := by
  change (if p 116 then d1115 (change p 162 (some 161)) else d1113 (change p 162 (some 161))) = d4838 p
  rw [sub6213, sub6211]
  rfl
theorem sub6215 (p : Pattern) : d268 (change p 162 (some 161)) = d268 p := by
  change (if p 204 then d116 (change p 162 (some 161)) else d103 (change p 162 (some 161))) = d268 p
  rw [sub6129, sub6124]
  rfl
theorem sub6216 (p : Pattern) : d269 (change p 162 (some 161)) = d269 p := by
  change (if p 182 then d117 (change p 162 (some 161)) else d268 (change p 162 (some 161))) = d269 p
  rw [sub6130, sub6215]
  rfl
theorem sub6217 (p : Pattern) : d291 (change p 162 (some 161)) = d291 p := by
  change (if p 163 then d269 (change p 162 (some 161)) else d105 (change p 162 (some 161))) = d291 p
  rw [sub6216, sub6126]
  rfl
theorem sub6218 (p : Pattern) : d1118 (change p 162 (some 161)) = d291 p := by
  change d291 (change p 162 (some 161)) = d291 p
  exact sub6217 p
theorem sub6219 (p : Pattern) : d1119 (change p 162 (some 161)) = d291 p := by
  change d1118 (change p 162 (some 161)) = d291 p
  exact sub6218 p
theorem sub6220 (p : Pattern) : d272 (change p 162 (some 161)) = d272 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d268 (change p 162 (some 161))) = d272 p
  rw [sub6009, sub6215]
  rfl
theorem sub6221 (p : Pattern) : d273 (change p 162 (some 161)) = d273 p := by
  change (if p 204 then d120 (change p 162 (some 161)) else d107 (change p 162 (some 161))) = d273 p
  rw [sub6153, sub6138]
  rfl
theorem sub6222 (p : Pattern) : d274 (change p 162 (some 161)) = d274 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d273 (change p 162 (some 161))) = d274 p
  rw [sub6009, sub6221]
  rfl
theorem sub6223 (p : Pattern) : d275 (change p 162 (some 161)) = d275 p := by
  change (if p 163 then d274 (change p 162 (some 161)) else d272 (change p 162 (some 161))) = d275 p
  rw [sub6222, sub6220]
  rfl
theorem sub6224 (p : Pattern) : d1121 (change p 162 (some 161)) = d275 p := by
  change d275 (change p 162 (some 161)) = d275 p
  exact sub6223 p
theorem sub6225 (p : Pattern) : d1122 (change p 162 (some 161)) = d275 p := by
  change d1121 (change p 162 (some 161)) = d275 p
  exact sub6224 p
theorem sub6226 (p : Pattern) : d1123 (change p 162 (some 161)) = d4841 p := by
  change (if p 160 then d1122 (change p 162 (some 161)) else d1119 (change p 162 (some 161))) = d4841 p
  rw [sub6225, sub6219]
  rfl
theorem sub6227 (p : Pattern) : d282 (change p 162 (some 161)) = d282 p := by
  change (if p 204 then d107 (change p 162 (some 161)) else d116 (change p 162 (some 161))) = d282 p
  rw [sub6138, sub6129]
  rfl
theorem sub6228 (p : Pattern) : d298 (change p 162 (some 161)) = d298 p := by
  change (if p 182 then d108 (change p 162 (some 161)) else d282 (change p 162 (some 161))) = d298 p
  rw [sub6145, sub6227]
  rfl
theorem sub6229 (p : Pattern) : d925 (change p 162 (some 161)) = d925 p := by
  change (if p 163 then d298 (change p 162 (some 161)) else d132 (change p 162 (some 161))) = d925 p
  rw [sub6228, sub6144]
  rfl
theorem sub6230 (p : Pattern) : d1124 (change p 162 (some 161)) = d925 p := by
  change d925 (change p 162 (some 161)) = d925 p
  exact sub6229 p
theorem sub6231 (p : Pattern) : d1125 (change p 162 (some 161)) = d925 p := by
  change d1124 (change p 162 (some 161)) = d925 p
  exact sub6230 p
theorem sub6232 (p : Pattern) : d283 (change p 162 (some 161)) = d283 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d282 (change p 162 (some 161))) = d283 p
  rw [sub6009, sub6227]
  rfl
theorem sub6233 (p : Pattern) : d9 (change p 162 (some 161)) = d9 p := by
  rfl
theorem sub6234 (p : Pattern) : d23 (change p 162 (some 161)) = d23 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d9 (change p 162 (some 161))) = d23 p
  rw [sub6009, sub6233]
  rfl
theorem sub6235 (p : Pattern) : d24 (change p 162 (some 161)) = d24 p := by
  change (if p 246 then d23 (change p 162 (some 161)) else d9 (change p 162 (some 161))) = d24 p
  rw [sub6234, sub6233]
  rfl
theorem sub6236 (p : Pattern) : d1126 (change p 162 (some 161)) = d1126 p := by
  change (if p 204 then d24 (change p 162 (some 161)) else d120 (change p 162 (some 161))) = d1126 p
  rw [sub6235, sub6153]
  rfl
theorem sub6237 (p : Pattern) : d1127 (change p 162 (some 161)) = d1127 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d1126 (change p 162 (some 161))) = d1127 p
  rw [sub6009, sub6236]
  rfl
theorem sub6238 (p : Pattern) : d1128 (change p 162 (some 161)) = d1128 p := by
  change (if p 163 then d1127 (change p 162 (some 161)) else d283 (change p 162 (some 161))) = d1128 p
  rw [sub6237, sub6232]
  rfl
theorem sub6239 (p : Pattern) : d1129 (change p 162 (some 161)) = d1128 p := by
  change d1128 (change p 162 (some 161)) = d1128 p
  exact sub6238 p
end NetHack.Sokoban22Refined85
