/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions43
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub5280 (p : Pattern) : d118 (change p 162 (some 163)) = d118 p := by
  change (if p 182 then d117 (change p 162 (some 163)) else d103 (change p 162 (some 163))) = d118 p
  rw [sub5279, sub5272]
  rfl
theorem sub5281 (p : Pattern) : d1043 (change p 162 (some 163)) = d118 p := by
  change d118 (change p 162 (some 163)) = d118 p
  exact sub5280 p
theorem sub5282 (p : Pattern) : d1044 (change p 162 (some 163)) = d118 p := by
  change d1043 (change p 162 (some 163)) = d118 p
  exact sub5281 p
theorem sub5283 (p : Pattern) : d1045 (change p 162 (some 163)) = d4697 p := by
  change (if p 161 then d1044 (change p 162 (some 163)) else d1042 (change p 162 (some 163))) = d4697 p
  rw [sub5282, sub5275]
  rfl
theorem sub5284 (p : Pattern) : d1046 (change p 162 (some 163)) = d118 p := by
  change d118 (change p 162 (some 163)) = d118 p
  exact sub5280 p
theorem sub5285 (p : Pattern) : d5 (change p 162 (some 163)) = d5 p := by
  rfl
theorem sub5286 (p : Pattern) : d106 (change p 162 (some 163)) = d106 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d5 (change p 162 (some 163))) = d106 p
  rw [sub5140, sub5285]
  rfl
theorem sub5287 (p : Pattern) : d107 (change p 162 (some 163)) = d107 p := by
  change (if p 246 then d106 (change p 162 (some 163)) else d5 (change p 162 (some 163))) = d107 p
  rw [sub5286, sub5285]
  rfl
theorem sub5288 (p : Pattern) : d125 (change p 162 (some 163)) = d125 p := by
  change (if p 182 then d12 (change p 162 (some 163)) else d107 (change p 162 (some 163))) = d125 p
  rw [sub5140, sub5287]
  rfl
theorem sub5289 (p : Pattern) : d126 (change p 162 (some 163)) = d125 p := by
  change d125 (change p 162 (some 163)) = d125 p
  exact sub5288 p
theorem sub5290 (p : Pattern) : d1047 (change p 162 (some 163)) = d125 p := by
  change d126 (change p 162 (some 163)) = d125 p
  exact sub5289 p
theorem sub5291 (p : Pattern) : d1048 (change p 162 (some 163)) = d4698 p := by
  change (if p 161 then d1047 (change p 162 (some 163)) else d1046 (change p 162 (some 163))) = d4698 p
  rw [sub5290, sub5284]
  rfl
theorem sub5292 (p : Pattern) : d1049 (change p 162 (some 163)) = d4699 p := by
  change (if p 160 then d1048 (change p 162 (some 163)) else d1045 (change p 162 (some 163))) = d4699 p
  rw [sub5291, sub5283]
  rfl
theorem sub5293 (p : Pattern) : d132 (change p 162 (some 163)) = d132 p := by
  change (if p 182 then d117 (change p 162 (some 163)) else d116 (change p 162 (some 163))) = d132 p
  rw [sub5279, sub5278]
  rfl
theorem sub5294 (p : Pattern) : d133 (change p 162 (some 163)) = d132 p := by
  change d132 (change p 162 (some 163)) = d132 p
  exact sub5293 p
theorem sub5295 (p : Pattern) : d1050 (change p 162 (some 163)) = d132 p := by
  change d133 (change p 162 (some 163)) = d132 p
  exact sub5294 p
theorem sub5296 (p : Pattern) : d108 (change p 162 (some 163)) = d108 p := by
  change (if p 204 then d12 (change p 162 (some 163)) else d107 (change p 162 (some 163))) = d108 p
  rw [sub5140, sub5287]
  rfl
theorem sub5297 (p : Pattern) : d861 (change p 162 (some 163)) = d861 p := by
  change (if p 182 then d108 (change p 162 (some 163)) else d116 (change p 162 (some 163))) = d861 p
  rw [sub5296, sub5278]
  rfl
theorem sub5298 (p : Pattern) : d862 (change p 162 (some 163)) = d861 p := by
  change d861 (change p 162 (some 163)) = d861 p
  exact sub5297 p
theorem sub5299 (p : Pattern) : d1051 (change p 162 (some 163)) = d861 p := by
  change d862 (change p 162 (some 163)) = d861 p
  exact sub5298 p
theorem sub5300 (p : Pattern) : d1052 (change p 162 (some 163)) = d4700 p := by
  change (if p 161 then d1051 (change p 162 (some 163)) else d1050 (change p 162 (some 163))) = d4700 p
  rw [sub5299, sub5295]
  rfl
theorem sub5301 (p : Pattern) : d7 (change p 162 (some 163)) = d7 p := by
  rfl
theorem sub5302 (p : Pattern) : d119 (change p 162 (some 163)) = d119 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d7 (change p 162 (some 163))) = d119 p
  rw [sub5140, sub5301]
  rfl
theorem sub5303 (p : Pattern) : d120 (change p 162 (some 163)) = d120 p := by
  change (if p 246 then d119 (change p 162 (some 163)) else d7 (change p 162 (some 163))) = d120 p
  rw [sub5302, sub5301]
  rfl
theorem sub5304 (p : Pattern) : d229 (change p 162 (some 163)) = d229 p := by
  change (if p 182 then d12 (change p 162 (some 163)) else d120 (change p 162 (some 163))) = d229 p
  rw [sub5140, sub5303]
  rfl
theorem sub5305 (p : Pattern) : d1053 (change p 162 (some 163)) = d229 p := by
  change d229 (change p 162 (some 163)) = d229 p
  exact sub5304 p
theorem sub5306 (p : Pattern) : d1054 (change p 162 (some 163)) = d229 p := by
  change d1053 (change p 162 (some 163)) = d229 p
  exact sub5305 p
theorem sub5307 (p : Pattern) : d1055 (change p 162 (some 163)) = d4701 p := by
  change (if p 161 then d1054 (change p 162 (some 163)) else d1051 (change p 162 (some 163))) = d4701 p
  rw [sub5306, sub5299]
  rfl
theorem sub5308 (p : Pattern) : d1056 (change p 162 (some 163)) = d4702 p := by
  change (if p 160 then d1055 (change p 162 (some 163)) else d1052 (change p 162 (some 163))) = d4702 p
  rw [sub5307, sub5300]
  rfl
theorem sub5309 (p : Pattern) : d1057 (change p 162 (some 163)) = d4703 p := by
  change (if p 141 then d1056 (change p 162 (some 163)) else d1049 (change p 162 (some 163))) = d4703 p
  rw [sub5308, sub5292]
  rfl
theorem sub5310 (p : Pattern) : d1058 (change p 162 (some 163)) = d105 p := by
  change d105 (change p 162 (some 163)) = d105 p
  exact sub5274 p
theorem sub5311 (p : Pattern) : d1059 (change p 162 (some 163)) = d132 p := by
  change d133 (change p 162 (some 163)) = d132 p
  exact sub5294 p
theorem sub5312 (p : Pattern) : d1060 (change p 162 (some 163)) = d4704 p := by
  change (if p 161 then d1059 (change p 162 (some 163)) else d1058 (change p 162 (some 163))) = d4704 p
  rw [sub5311, sub5310]
  rfl
theorem sub5313 (p : Pattern) : d1061 (change p 162 (some 163)) = d132 p := by
  change d132 (change p 162 (some 163)) = d132 p
  exact sub5293 p
theorem sub5314 (p : Pattern) : d1062 (change p 162 (some 163)) = d4705 p := by
  change (if p 161 then d12 (change p 162 (some 163)) else d1061 (change p 162 (some 163))) = d4705 p
  rw [sub5140, sub5313]
  rfl
theorem sub5315 (p : Pattern) : d1063 (change p 162 (some 163)) = d4706 p := by
  change (if p 160 then d1062 (change p 162 (some 163)) else d1060 (change p 162 (some 163))) = d4706 p
  rw [sub5314, sub5312]
  rfl
theorem sub5316 (p : Pattern) : d109 (change p 162 (some 163)) = d109 p := by
  change (if p 182 then d108 (change p 162 (some 163)) else d107 (change p 162 (some 163))) = d109 p
  rw [sub5296, sub5287]
  rfl
theorem sub5317 (p : Pattern) : d873 (change p 162 (some 163)) = d109 p := by
  change d109 (change p 162 (some 163)) = d109 p
  exact sub5316 p
theorem sub5318 (p : Pattern) : d1064 (change p 162 (some 163)) = d109 p := by
  change d873 (change p 162 (some 163)) = d109 p
  exact sub5317 p
theorem sub5319 (p : Pattern) : d1065 (change p 162 (some 163)) = d4707 p := by
  change (if p 161 then d1064 (change p 162 (some 163)) else d1059 (change p 162 (some 163))) = d4707 p
  rw [sub5318, sub5311]
  rfl
theorem sub5320 (p : Pattern) : d1066 (change p 162 (some 163)) = d4708 p := by
  change (if p 161 then d12 (change p 162 (some 163)) else d1064 (change p 162 (some 163))) = d4708 p
  rw [sub5140, sub5318]
  rfl
theorem sub5321 (p : Pattern) : d1067 (change p 162 (some 163)) = d4709 p := by
  change (if p 160 then d1066 (change p 162 (some 163)) else d1065 (change p 162 (some 163))) = d4709 p
  rw [sub5320, sub5319]
  rfl
theorem sub5322 (p : Pattern) : d1068 (change p 162 (some 163)) = d4710 p := by
  change (if p 141 then d1067 (change p 162 (some 163)) else d1063 (change p 162 (some 163))) = d4710 p
  rw [sub5321, sub5315]
  rfl
theorem sub5323 (p : Pattern) : d1069 (change p 162 (some 163)) = d4711 p := by
  change (if p 138 then d1068 (change p 162 (some 163)) else d1057 (change p 162 (some 163))) = d4711 p
  rw [sub5322, sub5309]
  rfl
theorem sub5324 (p : Pattern) : d1070 (change p 162 (some 163)) = d105 p := by
  change d105 (change p 162 (some 163)) = d105 p
  exact sub5274 p
theorem sub5325 (p : Pattern) : d1071 (change p 162 (some 163)) = d4704 p := by
  change (if p 161 then d1059 (change p 162 (some 163)) else d1070 (change p 162 (some 163))) = d4704 p
  rw [sub5311, sub5324]
  rfl
theorem sub5326 (p : Pattern) : d1072 (change p 162 (some 163)) = d4706 p := by
  change (if p 160 then d1062 (change p 162 (some 163)) else d1071 (change p 162 (some 163))) = d4706 p
  rw [sub5314, sub5325]
  rfl
theorem sub5327 (p : Pattern) : d1073 (change p 162 (some 163)) = d132 p := by
  change d133 (change p 162 (some 163)) = d132 p
  exact sub5294 p
theorem sub5328 (p : Pattern) : d1074 (change p 162 (some 163)) = d4707 p := by
  change (if p 161 then d1064 (change p 162 (some 163)) else d1073 (change p 162 (some 163))) = d4707 p
  rw [sub5318, sub5327]
  rfl
theorem sub5329 (p : Pattern) : d1075 (change p 162 (some 163)) = d4709 p := by
  change (if p 160 then d1066 (change p 162 (some 163)) else d1074 (change p 162 (some 163))) = d4709 p
  rw [sub5320, sub5328]
  rfl
theorem sub5330 (p : Pattern) : d1076 (change p 162 (some 163)) = d4710 p := by
  change (if p 141 then d1075 (change p 162 (some 163)) else d1072 (change p 162 (some 163))) = d4710 p
  rw [sub5329, sub5326]
  rfl
theorem sub5331 (p : Pattern) : d112 (change p 162 (some 163)) = d12 p := by
  change d12 (change p 162 (some 163)) = d12 p
  exact sub5140 p
theorem sub5332 (p : Pattern) : d159 (change p 162 (some 163)) = d12 p := by
  change d112 (change p 162 (some 163)) = d12 p
  exact sub5331 p
theorem sub5333 (p : Pattern) : d160 (change p 162 (some 163)) = d12 p := by
  change (if p 161 then d12 (change p 162 (some 163)) else d159 (change p 162 (some 163))) = d12 p
  rw [sub5140, sub5332]
  simp only [ite_self]
theorem sub5334 (p : Pattern) : d161 (change p 162 (some 163)) = d12 p := by
  change (if p 160 then d12 (change p 162 (some 163)) else d160 (change p 162 (some 163))) = d12 p
  rw [sub5140, sub5333]
  simp only [ite_self]
theorem sub5335 (p : Pattern) : d162 (change p 162 (some 163)) = d12 p := by
  change (if p 141 then d12 (change p 162 (some 163)) else d161 (change p 162 (some 163))) = d12 p
  rw [sub5140, sub5334]
  simp only [ite_self]
theorem sub5336 (p : Pattern) : d1077 (change p 162 (some 163)) = d4712 p := by
  change (if p 138 then d162 (change p 162 (some 163)) else d1076 (change p 162 (some 163))) = d4712 p
  rw [sub5335, sub5330]
  rfl
theorem sub5337 (p : Pattern) : d1078 (change p 162 (some 163)) = d4713 p := by
  change (if p 116 then d1077 (change p 162 (some 163)) else d1069 (change p 162 (some 163))) = d4713 p
  rw [sub5336, sub5323]
  rfl
theorem sub5338 (p : Pattern) : d1079 (change p 162 (some 163)) = d105 p := by
  change d105 (change p 162 (some 163)) = d105 p
  exact sub5274 p
theorem sub5339 (p : Pattern) : d1080 (change p 162 (some 163)) = d118 p := by
  change d1043 (change p 162 (some 163)) = d118 p
  exact sub5281 p
theorem sub5340 (p : Pattern) : d1081 (change p 162 (some 163)) = d4697 p := by
  change (if p 161 then d1080 (change p 162 (some 163)) else d1079 (change p 162 (some 163))) = d4697 p
  rw [sub5339, sub5338]
  rfl
theorem sub5341 (p : Pattern) : d1082 (change p 162 (some 163)) = d118 p := by
  change d118 (change p 162 (some 163)) = d118 p
  exact sub5280 p
theorem sub5342 (p : Pattern) : d1083 (change p 162 (some 163)) = d4698 p := by
  change (if p 161 then d1047 (change p 162 (some 163)) else d1082 (change p 162 (some 163))) = d4698 p
  rw [sub5290, sub5341]
  rfl
theorem sub5343 (p : Pattern) : d1084 (change p 162 (some 163)) = d4699 p := by
  change (if p 160 then d1083 (change p 162 (some 163)) else d1081 (change p 162 (some 163))) = d4699 p
  rw [sub5342, sub5340]
  rfl
theorem sub5344 (p : Pattern) : d1085 (change p 162 (some 163)) = d132 p := by
  change d133 (change p 162 (some 163)) = d132 p
  exact sub5294 p
theorem sub5345 (p : Pattern) : d1086 (change p 162 (some 163)) = d4700 p := by
  change (if p 161 then d1051 (change p 162 (some 163)) else d1085 (change p 162 (some 163))) = d4700 p
  rw [sub5299, sub5344]
  rfl
theorem sub5346 (p : Pattern) : d1087 (change p 162 (some 163)) = d4702 p := by
  change (if p 160 then d1055 (change p 162 (some 163)) else d1086 (change p 162 (some 163))) = d4702 p
  rw [sub5307, sub5345]
  rfl
theorem sub5347 (p : Pattern) : d1088 (change p 162 (some 163)) = d4703 p := by
  change (if p 141 then d1087 (change p 162 (some 163)) else d1084 (change p 162 (some 163))) = d4703 p
  rw [sub5346, sub5343]
  rfl
theorem sub5348 (p : Pattern) : d1089 (change p 162 (some 163)) = d105 p := by
  change d105 (change p 162 (some 163)) = d105 p
  exact sub5274 p
theorem sub5349 (p : Pattern) : d1090 (change p 162 (some 163)) = d4704 p := by
  change (if p 161 then d1059 (change p 162 (some 163)) else d1089 (change p 162 (some 163))) = d4704 p
  rw [sub5311, sub5348]
  rfl
theorem sub5350 (p : Pattern) : d1091 (change p 162 (some 163)) = d4706 p := by
  change (if p 160 then d1062 (change p 162 (some 163)) else d1090 (change p 162 (some 163))) = d4706 p
  rw [sub5314, sub5349]
  rfl
theorem sub5351 (p : Pattern) : d1092 (change p 162 (some 163)) = d4710 p := by
  change (if p 141 then d1067 (change p 162 (some 163)) else d1091 (change p 162 (some 163))) = d4710 p
  rw [sub5321, sub5350]
  rfl
theorem sub5352 (p : Pattern) : d1093 (change p 162 (some 163)) = d4711 p := by
  change (if p 138 then d1092 (change p 162 (some 163)) else d1088 (change p 162 (some 163))) = d4711 p
  rw [sub5351, sub5347]
  rfl
theorem sub5353 (p : Pattern) : d1094 (change p 162 (some 163)) = d4712 p := by
  change (if p 138 then d12 (change p 162 (some 163)) else d1092 (change p 162 (some 163))) = d4712 p
  rw [sub5140, sub5351]
  rfl
theorem sub5354 (p : Pattern) : d1095 (change p 162 (some 163)) = d4713 p := by
  change (if p 116 then d1094 (change p 162 (some 163)) else d1093 (change p 162 (some 163))) = d4713 p
  rw [sub5353, sub5352]
  rfl
theorem sub5355 (p : Pattern) : d1096 (change p 162 (some 163)) = d4713 p := by
  change (if p 115 then d1095 (change p 162 (some 163)) else d1078 (change p 162 (some 163))) = d4713 p
  rw [sub5354, sub5337]
  simp only [ite_self]
theorem sub5356 (p : Pattern) : d1097 (change p 162 (some 163)) = d4714 p := by
  change (if p 71 then d1096 (change p 162 (some 163)) else d1014 (change p 162 (some 163))) = d4714 p
  rw [sub5355, sub5242]
  rfl
theorem sub5357 (p : Pattern) : d1098 (change p 162 (some 163)) = d4715 p := by
  change (if p 49 then d1097 (change p 162 (some 163)) else d1041 (change p 162 (some 163))) = d4715 p
  rw [sub5356, sub5269]
  rfl
theorem sub5358 (p : Pattern) : d1099 (change p 162 (some 163)) = d4684 p := by
  change (if p 161 then d972 (change p 162 (some 163)) else d968 (change p 162 (some 163))) = d4684 p
  rw [sub5190, sub5184]
  rfl
theorem sub5359 (p : Pattern) : d1100 (change p 162 (some 163)) = d20 p := by
  change d20 (change p 162 (some 163)) = d20 p
  exact sub5188 p
theorem sub5360 (p : Pattern) : d1101 (change p 162 (some 163)) = d4685 p := by
  change (if p 161 then d12 (change p 162 (some 163)) else d1100 (change p 162 (some 163))) = d4685 p
  rw [sub5140, sub5359]
  rfl
theorem sub5361 (p : Pattern) : d1102 (change p 162 (some 163)) = d4686 p := by
  change (if p 160 then d1101 (change p 162 (some 163)) else d1099 (change p 162 (some 163))) = d4686 p
  rw [sub5360, sub5358]
  rfl
theorem sub5362 (p : Pattern) : d1103 (change p 162 (some 163)) = d4687 p := by
  change (if p 141 then d1102 (change p 162 (some 163)) else d1003 (change p 162 (some 163))) = d4687 p
  rw [sub5361, sub5231]
  rfl
theorem sub5363 (p : Pattern) : d1104 (change p 162 (some 163)) = d4688 p := by
  change (if p 138 then d1103 (change p 162 (some 163)) else d1036 (change p 162 (some 163))) = d4688 p
  rw [sub5362, sub5264]
  rfl
theorem sub5364 (p : Pattern) : d1105 (change p 162 (some 163)) = d4694 p := by
  change (if p 138 then d12 (change p 162 (some 163)) else d1103 (change p 162 (some 163))) = d4694 p
  rw [sub5140, sub5362]
  rfl
theorem sub5365 (p : Pattern) : d1106 (change p 162 (some 163)) = d4695 p := by
  change (if p 116 then d1105 (change p 162 (some 163)) else d1104 (change p 162 (some 163))) = d4695 p
  rw [sub5364, sub5363]
  rfl
theorem sub5366 (p : Pattern) : d1107 (change p 162 (some 163)) = d4696 p := by
  change (if p 115 then d1106 (change p 162 (some 163)) else d1031 (change p 162 (some 163))) = d4696 p
  rw [sub5365, sub5259]
  rfl
theorem sub5367 (p : Pattern) : d1108 (change p 162 (some 163)) = d4696 p := by
  change (if p 71 then d1107 (change p 162 (some 163)) else d1014 (change p 162 (some 163))) = d4696 p
  rw [sub5366, sub5242]
  simp only [ite_self]
theorem sub5368 (p : Pattern) : d1109 (change p 162 (some 163)) = d132 p := by
  change d133 (change p 162 (some 163)) = d132 p
  exact sub5294 p
theorem sub5369 (p : Pattern) : d1110 (change p 162 (some 163)) = d4700 p := by
  change (if p 161 then d1051 (change p 162 (some 163)) else d1109 (change p 162 (some 163))) = d4700 p
  rw [sub5299, sub5368]
  rfl
theorem sub5370 (p : Pattern) : d1111 (change p 162 (some 163)) = d4702 p := by
  change (if p 160 then d1055 (change p 162 (some 163)) else d1110 (change p 162 (some 163))) = d4702 p
  rw [sub5307, sub5369]
  rfl
theorem sub5371 (p : Pattern) : d1112 (change p 162 (some 163)) = d4703 p := by
  change (if p 141 then d1111 (change p 162 (some 163)) else d1049 (change p 162 (some 163))) = d4703 p
  rw [sub5370, sub5292]
  rfl
theorem sub5372 (p : Pattern) : d1113 (change p 162 (some 163)) = d4711 p := by
  change (if p 138 then d1068 (change p 162 (some 163)) else d1112 (change p 162 (some 163))) = d4711 p
  rw [sub5322, sub5371]
  rfl
theorem sub5373 (p : Pattern) : d1114 (change p 162 (some 163)) = d4710 p := by
  change (if p 141 then d1067 (change p 162 (some 163)) else d1072 (change p 162 (some 163))) = d4710 p
  rw [sub5321, sub5326]
  rfl
theorem sub5374 (p : Pattern) : d1115 (change p 162 (some 163)) = d4712 p := by
  change (if p 138 then d162 (change p 162 (some 163)) else d1114 (change p 162 (some 163))) = d4712 p
  rw [sub5335, sub5373]
  rfl
theorem sub5375 (p : Pattern) : d1116 (change p 162 (some 163)) = d4713 p := by
  change (if p 116 then d1115 (change p 162 (some 163)) else d1113 (change p 162 (some 163))) = d4713 p
  rw [sub5374, sub5372]
  rfl
theorem sub5376 (p : Pattern) : d1117 (change p 162 (some 163)) = d105 p := by
  change d105 (change p 162 (some 163)) = d105 p
  exact sub5274 p
theorem sub5377 (p : Pattern) : d268 (change p 162 (some 163)) = d268 p := by
  change (if p 204 then d116 (change p 162 (some 163)) else d103 (change p 162 (some 163))) = d268 p
  rw [sub5278, sub5272]
  rfl
theorem sub5378 (p : Pattern) : d269 (change p 162 (some 163)) = d269 p := by
  change (if p 182 then d117 (change p 162 (some 163)) else d268 (change p 162 (some 163))) = d269 p
  rw [sub5279, sub5377]
  rfl
theorem sub5379 (p : Pattern) : d291 (change p 162 (some 163)) = d269 p := by
  change d269 (change p 162 (some 163)) = d269 p
  exact sub5378 p
theorem sub5380 (p : Pattern) : d1118 (change p 162 (some 163)) = d269 p := by
  change d291 (change p 162 (some 163)) = d269 p
  exact sub5379 p
theorem sub5381 (p : Pattern) : d1119 (change p 162 (some 163)) = d4716 p := by
  change (if p 161 then d1118 (change p 162 (some 163)) else d1117 (change p 162 (some 163))) = d4716 p
  rw [sub5380, sub5376]
  rfl
theorem sub5382 (p : Pattern) : d1120 (change p 162 (some 163)) = d269 p := by
  change d269 (change p 162 (some 163)) = d269 p
  exact sub5378 p
theorem sub5383 (p : Pattern) : d273 (change p 162 (some 163)) = d273 p := by
  change (if p 204 then d120 (change p 162 (some 163)) else d107 (change p 162 (some 163))) = d273 p
  rw [sub5303, sub5287]
  rfl
theorem sub5384 (p : Pattern) : d274 (change p 162 (some 163)) = d274 p := by
  change (if p 182 then d12 (change p 162 (some 163)) else d273 (change p 162 (some 163))) = d274 p
  rw [sub5140, sub5383]
  rfl
theorem sub5385 (p : Pattern) : d275 (change p 162 (some 163)) = d274 p := by
  change d274 (change p 162 (some 163)) = d274 p
  exact sub5384 p
theorem sub5386 (p : Pattern) : d1121 (change p 162 (some 163)) = d274 p := by
  change d275 (change p 162 (some 163)) = d274 p
  exact sub5385 p
theorem sub5387 (p : Pattern) : d1122 (change p 162 (some 163)) = d4717 p := by
  change (if p 161 then d1121 (change p 162 (some 163)) else d1120 (change p 162 (some 163))) = d4717 p
  rw [sub5386, sub5382]
  rfl
theorem sub5388 (p : Pattern) : d1123 (change p 162 (some 163)) = d4718 p := by
  change (if p 160 then d1122 (change p 162 (some 163)) else d1119 (change p 162 (some 163))) = d4718 p
  rw [sub5387, sub5381]
  rfl
theorem sub5389 (p : Pattern) : d282 (change p 162 (some 163)) = d282 p := by
  change (if p 204 then d107 (change p 162 (some 163)) else d116 (change p 162 (some 163))) = d282 p
  rw [sub5287, sub5278]
  rfl
theorem sub5390 (p : Pattern) : d298 (change p 162 (some 163)) = d298 p := by
  change (if p 182 then d108 (change p 162 (some 163)) else d282 (change p 162 (some 163))) = d298 p
  rw [sub5296, sub5389]
  rfl
theorem sub5391 (p : Pattern) : d925 (change p 162 (some 163)) = d298 p := by
  change d298 (change p 162 (some 163)) = d298 p
  exact sub5390 p
theorem sub5392 (p : Pattern) : d1124 (change p 162 (some 163)) = d298 p := by
  change d925 (change p 162 (some 163)) = d298 p
  exact sub5391 p
theorem sub5393 (p : Pattern) : d1125 (change p 162 (some 163)) = d4719 p := by
  change (if p 161 then d1124 (change p 162 (some 163)) else d1059 (change p 162 (some 163))) = d4719 p
  rw [sub5392, sub5311]
  rfl
theorem sub5394 (p : Pattern) : d9 (change p 162 (some 163)) = d9 p := by
  rfl
theorem sub5395 (p : Pattern) : d23 (change p 162 (some 163)) = d23 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d9 (change p 162 (some 163))) = d23 p
  rw [sub5140, sub5394]
  rfl
theorem sub5396 (p : Pattern) : d24 (change p 162 (some 163)) = d24 p := by
  change (if p 246 then d23 (change p 162 (some 163)) else d9 (change p 162 (some 163))) = d24 p
  rw [sub5395, sub5394]
  rfl
theorem sub5397 (p : Pattern) : d1126 (change p 162 (some 163)) = d1126 p := by
  change (if p 204 then d24 (change p 162 (some 163)) else d120 (change p 162 (some 163))) = d1126 p
  rw [sub5396, sub5303]
  rfl
theorem sub5398 (p : Pattern) : d1127 (change p 162 (some 163)) = d1127 p := by
  change (if p 182 then d12 (change p 162 (some 163)) else d1126 (change p 162 (some 163))) = d1127 p
  rw [sub5140, sub5397]
  rfl
theorem sub5399 (p : Pattern) : d1128 (change p 162 (some 163)) = d1127 p := by
  change d1127 (change p 162 (some 163)) = d1127 p
  exact sub5398 p
end NetHack.Sokoban22Refined85
