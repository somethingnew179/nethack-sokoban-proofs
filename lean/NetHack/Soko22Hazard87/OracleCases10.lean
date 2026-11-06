import NetHack.Soko22Hazard87.OracleCases09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases1000 : List OracleBranch := []
noncomputable def rowCases1001 : List OracleBranch := []
noncomputable def rowCases1002 : List OracleBranch := [((.walk 251), d378991), ((.push 251 (.fill 252)), d379135), ((.push 251 (.stay 252)), d379271)]
theorem oracleMember995 : ((.walk 251), d378991) ∈ rowCases1002 := by
  exact List.mem_cons_self
theorem oracleMember996 : ((.push 251 (.fill 252)), d379135) ∈ rowCases1002 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember997 : ((.push 251 (.stay 252)), d379271) ∈ rowCases1002 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1003 : List OracleBranch := [((.walk 249), d375596), ((.push 249 (.stay 248)), d370936)]
theorem oracleMember998 : ((.walk 249), d375596) ∈ rowCases1003 := by
  exact List.mem_cons_self
theorem oracleMember999 : ((.push 249 (.stay 248)), d370936) ∈ rowCases1003 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases1004 : List OracleBranch := []
noncomputable def rowCases1005 : List OracleBranch := []
noncomputable def rowCases1006 : List OracleBranch := []
noncomputable def rowCases1007 : List OracleBranch := []
noncomputable def rowCases1008 : List OracleBranch := []
noncomputable def rowCases1009 : List OracleBranch := []
noncomputable def rowCases1010 : List OracleBranch := [((.walk 252), d379277), ((.push 252 (.fill 253)), d379424), ((.push 252 (.stay 253)), d379563)]
theorem oracleMember1000 : ((.walk 252), d379277) ∈ rowCases1010 := by
  exact List.mem_cons_self
theorem oracleMember1001 : ((.push 252 (.fill 253)), d379424) ∈ rowCases1010 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1002 : ((.push 252 (.stay 253)), d379563) ∈ rowCases1010 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1011 : List OracleBranch := [((.walk 250), d378991), ((.push 250 (.stay 245)), d379577)]
theorem oracleMember1003 : ((.walk 250), d378991) ∈ rowCases1011 := by
  exact List.mem_cons_self
theorem oracleMember1004 : ((.push 250 (.stay 245)), d379577) ∈ rowCases1011 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases1012 : List OracleBranch := []
noncomputable def rowCases1013 : List OracleBranch := []
noncomputable def rowCases1014 : List OracleBranch := []
noncomputable def rowCases1015 : List OracleBranch := []
noncomputable def rowCases1016 : List OracleBranch := []
noncomputable def rowCases1017 : List OracleBranch := []
noncomputable def rowCases1018 : List OracleBranch := [((.walk 253), d379583), ((.push 253 (.fill 254)), d379733), ((.push 253 (.stay 254)), d379875)]
theorem oracleMember1005 : ((.walk 253), d379583) ∈ rowCases1018 := by
  exact List.mem_cons_self
theorem oracleMember1006 : ((.push 253 (.fill 254)), d379733) ∈ rowCases1018 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1007 : ((.push 253 (.stay 254)), d379875) ∈ rowCases1018 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1019 : List OracleBranch := [((.walk 251), d379277), ((.push 251 (.fill 250)), d379882), ((.push 251 (.stay 250)), d379271)]
theorem oracleMember1008 : ((.walk 251), d379277) ∈ rowCases1019 := by
  exact List.mem_cons_self
theorem oracleMember1009 : ((.push 251 (.fill 250)), d379882) ∈ rowCases1019 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1010 : ((.push 251 (.stay 250)), d379271) ∈ rowCases1019 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1020 : List OracleBranch := []
noncomputable def rowCases1021 : List OracleBranch := []
noncomputable def rowCases1022 : List OracleBranch := []
noncomputable def rowCases1023 : List OracleBranch := []
noncomputable def rowCases1024 : List OracleBranch := []
noncomputable def rowCases1025 : List OracleBranch := []
noncomputable def rowCases1026 : List OracleBranch := [((.walk 254), d380014), ((.push 254 (.fill 255)), d380167), ((.push 254 (.stay 255)), d380312)]
theorem oracleMember1011 : ((.walk 254), d380014) ∈ rowCases1026 := by
  exact List.mem_cons_self
theorem oracleMember1012 : ((.push 254 (.fill 255)), d380167) ∈ rowCases1026 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1013 : ((.push 254 (.stay 255)), d380312) ∈ rowCases1026 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1027 : List OracleBranch := [((.walk 252), d379583), ((.push 252 (.fill 251)), d380319), ((.push 252 (.stay 251)), d379563)]
theorem oracleMember1014 : ((.walk 252), d379583) ∈ rowCases1027 := by
  exact List.mem_cons_self
theorem oracleMember1015 : ((.push 252 (.fill 251)), d380319) ∈ rowCases1027 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1016 : ((.push 252 (.stay 251)), d379563) ∈ rowCases1027 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1028 : List OracleBranch := []
noncomputable def rowCases1029 : List OracleBranch := []
noncomputable def rowCases1030 : List OracleBranch := []
noncomputable def rowCases1031 : List OracleBranch := []
noncomputable def rowCases1032 : List OracleBranch := []
noncomputable def rowCases1033 : List OracleBranch := []
noncomputable def rowCases1034 : List OracleBranch := [((.walk 255), d380454), ((.push 255 (.fill 256)), d380610), ((.push 255 (.stay 256)), d380710)]
theorem oracleMember1017 : ((.walk 255), d380454) ∈ rowCases1034 := by
  exact List.mem_cons_self
theorem oracleMember1018 : ((.push 255 (.fill 256)), d380610) ∈ rowCases1034 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1019 : ((.push 255 (.stay 256)), d380710) ∈ rowCases1034 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1035 : List OracleBranch := [((.walk 253), d380014), ((.push 253 (.fill 252)), d380717), ((.push 253 (.stay 252)), d379875)]
theorem oracleMember1020 : ((.walk 253), d380014) ∈ rowCases1035 := by
  exact List.mem_cons_self
theorem oracleMember1021 : ((.push 253 (.fill 252)), d380717) ∈ rowCases1035 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1022 : ((.push 253 (.stay 252)), d379875) ∈ rowCases1035 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1036 : List OracleBranch := []
noncomputable def rowCases1037 : List OracleBranch := []
noncomputable def rowCases1038 : List OracleBranch := []
noncomputable def rowCases1039 : List OracleBranch := []
noncomputable def rowCases1040 : List OracleBranch := []
noncomputable def rowCases1041 : List OracleBranch := []
noncomputable def rowCases1042 : List OracleBranch := [((.walk 256), d380855), ((.push 256 (.fill 257)), d380914), ((.push 256 (.stay 257)), d380918)]
theorem oracleMember1023 : ((.walk 256), d380855) ∈ rowCases1042 := by
  exact List.mem_cons_self
theorem oracleMember1024 : ((.push 256 (.fill 257)), d380914) ∈ rowCases1042 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1025 : ((.push 256 (.stay 257)), d380918) ∈ rowCases1042 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1043 : List OracleBranch := [((.walk 254), d380454), ((.push 254 (.fill 253)), d380925), ((.push 254 (.stay 253)), d380312)]
theorem oracleMember1026 : ((.walk 254), d380454) ∈ rowCases1043 := by
  exact List.mem_cons_self
theorem oracleMember1027 : ((.push 254 (.fill 253)), d380925) ∈ rowCases1043 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1028 : ((.push 254 (.stay 253)), d380312) ∈ rowCases1043 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1044 : List OracleBranch := []
noncomputable def rowCases1045 : List OracleBranch := []
noncomputable def rowCases1046 : List OracleBranch := []
noncomputable def rowCases1047 : List OracleBranch := []
noncomputable def rowCases1048 : List OracleBranch := []
noncomputable def rowCases1049 : List OracleBranch := []
noncomputable def rowCases1050 : List OracleBranch := [((.walk 257), d381066), ((.push 257 (.fill 258)), d381075), ((.push 257 (.stay 258)), d381079)]
theorem oracleMember1029 : ((.walk 257), d381066) ∈ rowCases1050 := by
  exact List.mem_cons_self
theorem oracleMember1030 : ((.push 257 (.fill 258)), d381075) ∈ rowCases1050 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1031 : ((.push 257 (.stay 258)), d381079) ∈ rowCases1050 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1051 : List OracleBranch := [((.walk 255), d380855), ((.push 255 (.fill 254)), d381086), ((.push 255 (.stay 254)), d380710)]
theorem oracleMember1032 : ((.walk 255), d380855) ∈ rowCases1051 := by
  exact List.mem_cons_self
theorem oracleMember1033 : ((.push 255 (.fill 254)), d381086) ∈ rowCases1051 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1034 : ((.push 255 (.stay 254)), d380710) ∈ rowCases1051 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1052 : List OracleBranch := []
noncomputable def rowCases1053 : List OracleBranch := []
noncomputable def rowCases1054 : List OracleBranch := []
noncomputable def rowCases1055 : List OracleBranch := []
noncomputable def rowCases1056 : List OracleBranch := []
noncomputable def rowCases1057 : List OracleBranch := []
noncomputable def rowCases1058 : List OracleBranch := [((.walk 258), d381230), ((.push 258 (.fill 259)), d381239), ((.push 258 (.stay 259)), d381243)]
theorem oracleMember1035 : ((.walk 258), d381230) ∈ rowCases1058 := by
  exact List.mem_cons_self
theorem oracleMember1036 : ((.push 258 (.fill 259)), d381239) ∈ rowCases1058 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1037 : ((.push 258 (.stay 259)), d381243) ∈ rowCases1058 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1059 : List OracleBranch := [((.walk 256), d381066), ((.push 256 (.fill 255)), d381250), ((.push 256 (.stay 255)), d380918)]
theorem oracleMember1038 : ((.walk 256), d381066) ∈ rowCases1059 := by
  exact List.mem_cons_self
theorem oracleMember1039 : ((.push 256 (.fill 255)), d381250) ∈ rowCases1059 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1040 : ((.push 256 (.stay 255)), d380918) ∈ rowCases1059 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1060 : List OracleBranch := []
noncomputable def rowCases1061 : List OracleBranch := []
noncomputable def rowCases1062 : List OracleBranch := []
noncomputable def rowCases1063 : List OracleBranch := []
noncomputable def rowCases1064 : List OracleBranch := []
noncomputable def rowCases1065 : List OracleBranch := []
noncomputable def rowCases1066 : List OracleBranch := [((.walk 259), d381350), ((.push 259 (.fill 260)), d381359), ((.push 259 (.stay 260)), d381363)]
theorem oracleMember1041 : ((.walk 259), d381350) ∈ rowCases1066 := by
  exact List.mem_cons_self
theorem oracleMember1042 : ((.push 259 (.fill 260)), d381359) ∈ rowCases1066 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1043 : ((.push 259 (.stay 260)), d381363) ∈ rowCases1066 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1067 : List OracleBranch := [((.walk 257), d381230), ((.push 257 (.fill 256)), d381370), ((.push 257 (.stay 256)), d381079)]
theorem oracleMember1044 : ((.walk 257), d381230) ∈ rowCases1067 := by
  exact List.mem_cons_self
theorem oracleMember1045 : ((.push 257 (.fill 256)), d381370) ∈ rowCases1067 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1046 : ((.push 257 (.stay 256)), d381079) ∈ rowCases1067 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1068 : List OracleBranch := []
noncomputable def rowCases1069 : List OracleBranch := []
noncomputable def rowCases1070 : List OracleBranch := []
noncomputable def rowCases1071 : List OracleBranch := []
noncomputable def rowCases1072 : List OracleBranch := []
noncomputable def rowCases1073 : List OracleBranch := []
noncomputable def rowCases1074 : List OracleBranch := [((.walk 260), d381376)]
theorem oracleMember1047 : ((.walk 260), d381376) ∈ rowCases1074 := by
  exact List.mem_cons_self
noncomputable def rowCases1075 : List OracleBranch := [((.walk 258), d381350), ((.push 258 (.fill 257)), d381383), ((.push 258 (.stay 257)), d381243)]
theorem oracleMember1048 : ((.walk 258), d381350) ∈ rowCases1075 := by
  exact List.mem_cons_self
theorem oracleMember1049 : ((.push 258 (.fill 257)), d381383) ∈ rowCases1075 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1050 : ((.push 258 (.stay 257)), d381243) ∈ rowCases1075 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1076 : List OracleBranch := []
noncomputable def rowCases1077 : List OracleBranch := []
noncomputable def rowCases1078 : List OracleBranch := []
noncomputable def rowCases1079 : List OracleBranch := []
noncomputable def rowCases1080 : List OracleBranch := []
noncomputable def rowCases1081 : List OracleBranch := []
noncomputable def rowCases1082 : List OracleBranch := []
noncomputable def rowCases1083 : List OracleBranch := [((.walk 259), d381376), ((.push 259 (.fill 258)), d381391), ((.push 259 (.stay 258)), d381363)]
theorem oracleMember1051 : ((.walk 259), d381376) ∈ rowCases1083 := by
  exact List.mem_cons_self
theorem oracleMember1052 : ((.push 259 (.fill 258)), d381391) ∈ rowCases1083 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember1053 : ((.push 259 (.stay 258)), d381363) ∈ rowCases1083 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases1084 : List OracleBranch := []
noncomputable def rowCases1085 : List OracleBranch := []
noncomputable def rowCases1086 : List OracleBranch := []
noncomputable def rowCases1087 : List OracleBranch := []
noncomputable def rowCases1088 : List OracleBranch := [((.walk 240), d1), ((.push 240 (.stay 218)), d0)]
theorem oracleMember1054 : ((.walk 240), d1) ∈ rowCases1088 := by
  exact List.mem_cons_self
theorem oracleMember1055 : ((.push 240 (.stay 218)), d0) ∈ rowCases1088 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases1089 : List OracleBranch := []
noncomputable def rowCases1090 : List OracleBranch := []
noncomputable def rowCases1091 : List OracleBranch := []
noncomputable def rowCases1092 : List OracleBranch := []
noncomputable def rowCases1093 : List OracleBranch := []
noncomputable def rowCases1094 : List OracleBranch := []
noncomputable def rowCases1095 : List OracleBranch := []
end NetHack.Soko22Hazard87
