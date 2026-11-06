import NetHack.Soko22Hazard87.OracleCases08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases900 : List OracleBranch := [((.walk 194), d1)]
theorem oracleMember910 : ((.walk 194), d1) ∈ rowCases900 := by
  exact List.mem_cons_self
noncomputable def rowCases901 : List OracleBranch := [((.walk 192), d1)]
theorem oracleMember911 : ((.walk 192), d1) ∈ rowCases901 := by
  exact List.mem_cons_self
noncomputable def rowCases902 : List OracleBranch := []
noncomputable def rowCases903 : List OracleBranch := []
noncomputable def rowCases904 : List OracleBranch := [((.walk 194), d1), ((.push 194 (.stay 172)), d0)]
theorem oracleMember912 : ((.walk 194), d1) ∈ rowCases904 := by
  exact List.mem_cons_self
theorem oracleMember913 : ((.push 194 (.stay 172)), d0) ∈ rowCases904 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases905 : List OracleBranch := []
noncomputable def rowCases906 : List OracleBranch := []
noncomputable def rowCases907 : List OracleBranch := [((.walk 215), d1), ((.push 215 (.stay 214)), d0)]
theorem oracleMember914 : ((.walk 215), d1) ∈ rowCases907 := by
  exact List.mem_cons_self
theorem oracleMember915 : ((.push 215 (.stay 214)), d0) ∈ rowCases907 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases908 : List OracleBranch := []
noncomputable def rowCases909 : List OracleBranch := [((.walk 193), d1)]
theorem oracleMember916 : ((.walk 193), d1) ∈ rowCases909 := by
  exact List.mem_cons_self
noncomputable def rowCases910 : List OracleBranch := []
noncomputable def rowCases911 : List OracleBranch := []
noncomputable def rowCases912 : List OracleBranch := []
noncomputable def rowCases913 : List OracleBranch := [((.walk 240), d1), ((.push 240 (.stay 262)), d0)]
theorem oracleMember917 : ((.walk 240), d1) ∈ rowCases913 := by
  exact List.mem_cons_self
theorem oracleMember918 : ((.push 240 (.stay 262)), d0) ∈ rowCases913 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases914 : List OracleBranch := []
noncomputable def rowCases915 : List OracleBranch := []
noncomputable def rowCases916 : List OracleBranch := []
noncomputable def rowCases917 : List OracleBranch := []
noncomputable def rowCases918 : List OracleBranch := []
noncomputable def rowCases919 : List OracleBranch := []
noncomputable def rowCases920 : List OracleBranch := [((.walk 201), d236582)]
theorem oracleMember919 : ((.walk 201), d236582) ∈ rowCases920 := by
  exact List.mem_cons_self
noncomputable def rowCases921 : List OracleBranch := [((.walk 245), d279951)]
theorem oracleMember920 : ((.walk 245), d279951) ∈ rowCases921 := by
  exact List.mem_cons_self
noncomputable def rowCases922 : List OracleBranch := [((.walk 224), d241830), ((.push 224 (.stay 225)), d282284)]
theorem oracleMember921 : ((.walk 224), d241830) ∈ rowCases922 := by
  exact List.mem_cons_self
theorem oracleMember922 : ((.push 224 (.stay 225)), d282284) ∈ rowCases922 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases923 : List OracleBranch := []
noncomputable def rowCases924 : List OracleBranch := [((.walk 202), d266246)]
theorem oracleMember923 : ((.walk 202), d266246) ∈ rowCases924 := by
  exact List.mem_cons_self
noncomputable def rowCases925 : List OracleBranch := [((.walk 200), d236583)]
theorem oracleMember924 : ((.walk 200), d236583) ∈ rowCases925 := by
  exact List.mem_cons_self
noncomputable def rowCases926 : List OracleBranch := [((.walk 246), d287737)]
theorem oracleMember925 : ((.walk 246), d287737) ∈ rowCases926 := by
  exact List.mem_cons_self
noncomputable def rowCases927 : List OracleBranch := []
noncomputable def rowCases928 : List OracleBranch := [((.walk 202), d251389), ((.push 202 (.stay 180)), d202307)]
theorem oracleMember926 : ((.walk 202), d251389) ∈ rowCases928 := by
  exact List.mem_cons_self
theorem oracleMember927 : ((.push 202 (.stay 180)), d202307) ∈ rowCases928 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases929 : List OracleBranch := [((.walk 246), d287735)]
theorem oracleMember928 : ((.walk 246), d287735) ∈ rowCases929 := by
  exact List.mem_cons_self
noncomputable def rowCases930 : List OracleBranch := [((.walk 225), d261985), ((.push 225 (.stay 226)), d300100)]
theorem oracleMember929 : ((.walk 225), d261985) ∈ rowCases930 := by
  exact List.mem_cons_self
theorem oracleMember930 : ((.push 225 (.stay 226)), d300100) ∈ rowCases930 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases931 : List OracleBranch := [((.walk 223), d241830)]
theorem oracleMember931 : ((.walk 223), d241830) ∈ rowCases931 := by
  exact List.mem_cons_self
noncomputable def rowCases932 : List OracleBranch := []
noncomputable def rowCases933 : List OracleBranch := [((.walk 201), d241832)]
theorem oracleMember932 : ((.walk 201), d241832) ∈ rowCases933 := by
  exact List.mem_cons_self
noncomputable def rowCases934 : List OracleBranch := [((.walk 247), d306035)]
theorem oracleMember933 : ((.walk 247), d306035) ∈ rowCases934 := by
  exact List.mem_cons_self
noncomputable def rowCases935 : List OracleBranch := [((.walk 245), d310057)]
theorem oracleMember934 : ((.walk 245), d310057) ∈ rowCases935 := by
  exact List.mem_cons_self
noncomputable def rowCases936 : List OracleBranch := []
noncomputable def rowCases937 : List OracleBranch := [((.walk 247), d310774)]
theorem oracleMember935 : ((.walk 247), d310774) ∈ rowCases937 := by
  exact List.mem_cons_self
noncomputable def rowCases938 : List OracleBranch := [((.walk 226), d277739)]
theorem oracleMember936 : ((.walk 226), d277739) ∈ rowCases938 := by
  exact List.mem_cons_self
noncomputable def rowCases939 : List OracleBranch := [((.walk 224), d261985), ((.push 224 (.stay 223)), d282284)]
theorem oracleMember937 : ((.walk 224), d261985) ∈ rowCases939 := by
  exact List.mem_cons_self
theorem oracleMember938 : ((.push 224 (.stay 223)), d282284) ∈ rowCases939 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases940 : List OracleBranch := [((.walk 204), d277740)]
theorem oracleMember939 : ((.walk 204), d277740) ∈ rowCases940 := by
  exact List.mem_cons_self
noncomputable def rowCases941 : List OracleBranch := [((.walk 202), d261986)]
theorem oracleMember940 : ((.walk 202), d261986) ∈ rowCases941 := by
  exact List.mem_cons_self
noncomputable def rowCases942 : List OracleBranch := [((.walk 248), d318725)]
theorem oracleMember941 : ((.walk 248), d318725) ∈ rowCases942 := by
  exact List.mem_cons_self
noncomputable def rowCases943 : List OracleBranch := [((.walk 246), d322255)]
theorem oracleMember942 : ((.walk 246), d322255) ∈ rowCases943 := by
  exact List.mem_cons_self
noncomputable def rowCases944 : List OracleBranch := [((.walk 204), d267844), ((.push 204 (.stay 182)), d216471)]
theorem oracleMember943 : ((.walk 204), d267844) ∈ rowCases944 := by
  exact List.mem_cons_self
theorem oracleMember944 : ((.push 204 (.stay 182)), d216471) ∈ rowCases944 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases945 : List OracleBranch := [((.walk 248), d325306)]
theorem oracleMember945 : ((.walk 248), d325306) ∈ rowCases945 := by
  exact List.mem_cons_self
noncomputable def rowCases946 : List OracleBranch := []
noncomputable def rowCases947 : List OracleBranch := [((.walk 225), d277739), ((.push 225 (.stay 224)), d300100)]
theorem oracleMember946 : ((.walk 225), d277739) ∈ rowCases947 := by
  exact List.mem_cons_self
theorem oracleMember947 : ((.push 225 (.stay 224)), d300100) ∈ rowCases947 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases948 : List OracleBranch := []
noncomputable def rowCases949 : List OracleBranch := []
noncomputable def rowCases950 : List OracleBranch := [((.walk 249), d331330)]
theorem oracleMember948 : ((.walk 249), d331330) ∈ rowCases950 := by
  exact List.mem_cons_self
noncomputable def rowCases951 : List OracleBranch := [((.walk 247), d331335)]
theorem oracleMember949 : ((.walk 247), d331335) ∈ rowCases951 := by
  exact List.mem_cons_self
noncomputable def rowCases952 : List OracleBranch := [((.walk 218), d1)]
theorem oracleMember950 : ((.walk 218), d1) ∈ rowCases952 := by
  exact List.mem_cons_self
noncomputable def rowCases953 : List OracleBranch := [((.walk 262), d1)]
theorem oracleMember951 : ((.walk 262), d1) ∈ rowCases953 := by
  exact List.mem_cons_self
noncomputable def rowCases954 : List OracleBranch := []
noncomputable def rowCases955 : List OracleBranch := []
noncomputable def rowCases956 : List OracleBranch := []
noncomputable def rowCases957 : List OracleBranch := []
noncomputable def rowCases958 : List OracleBranch := []
noncomputable def rowCases959 : List OracleBranch := []
noncomputable def rowCases960 : List OracleBranch := [((.walk 223), d279951), ((.push 223 (.stay 201)), d239127)]
theorem oracleMember952 : ((.walk 223), d279951) ∈ rowCases960 := by
  exact List.mem_cons_self
theorem oracleMember953 : ((.push 223 (.stay 201)), d239127) ∈ rowCases960 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases961 : List OracleBranch := []
noncomputable def rowCases962 : List OracleBranch := [((.walk 246), d338547), ((.push 246 (.stay 247)), d338652)]
theorem oracleMember954 : ((.walk 246), d338547) ∈ rowCases962 := by
  exact List.mem_cons_self
theorem oracleMember955 : ((.push 246 (.stay 247)), d338652) ∈ rowCases962 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases963 : List OracleBranch := []
noncomputable def rowCases964 : List OracleBranch := [((.walk 224), d310057)]
theorem oracleMember956 : ((.walk 224), d310057) ∈ rowCases964 := by
  exact List.mem_cons_self
noncomputable def rowCases965 : List OracleBranch := []
noncomputable def rowCases966 : List OracleBranch := []
noncomputable def rowCases967 : List OracleBranch := []
noncomputable def rowCases968 : List OracleBranch := [((.walk 224), d287735), ((.push 224 (.stay 202)), d253272)]
theorem oracleMember957 : ((.walk 224), d287735) ∈ rowCases968 := by
  exact List.mem_cons_self
theorem oracleMember958 : ((.push 224 (.stay 202)), d253272) ∈ rowCases968 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases969 : List OracleBranch := []
noncomputable def rowCases970 : List OracleBranch := [((.walk 247), d271214), ((.push 247 (.stay 248)), d46864)]
theorem oracleMember959 : ((.walk 247), d271214) ∈ rowCases970 := by
  exact List.mem_cons_self
theorem oracleMember960 : ((.push 247 (.stay 248)), d46864) ∈ rowCases970 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases971 : List OracleBranch := [((.walk 245), d338547)]
theorem oracleMember961 : ((.walk 245), d338547) ∈ rowCases971 := by
  exact List.mem_cons_self
noncomputable def rowCases972 : List OracleBranch := [((.walk 225), d322255)]
theorem oracleMember962 : ((.walk 225), d322255) ∈ rowCases972 := by
  exact List.mem_cons_self
noncomputable def rowCases973 : List OracleBranch := [((.walk 223), d287737)]
theorem oracleMember963 : ((.walk 223), d287737) ∈ rowCases973 := by
  exact List.mem_cons_self
noncomputable def rowCases974 : List OracleBranch := []
noncomputable def rowCases975 : List OracleBranch := []
noncomputable def rowCases976 : List OracleBranch := [((.walk 225), d310774)]
theorem oracleMember964 : ((.walk 225), d310774) ∈ rowCases976 := by
  exact List.mem_cons_self
noncomputable def rowCases977 : List OracleBranch := []
noncomputable def rowCases978 : List OracleBranch := [((.walk 248), d14), ((.push 248 (.fill 250)), d358937), ((.push 248 (.fill 251)), d363235), ((.push 248 (.fill 252)), d363819), ((.push 248 (.fill 253)), d364421), ((.push 248 (.fill 254)), d364965), ((.push 248 (.fill 255)), d365448), ((.push 248 (.fill 256)), d365809), ((.push 248 (.fill 257)), d366034), ((.push 248 (.fill 258)), d366084), ((.push 248 (.fill 259)), d366139), ((.push 248 (.fill 260)), d366199)]
theorem oracleMember965 : ((.walk 248), d14) ∈ rowCases978 := by
  exact List.mem_cons_self
theorem oracleMember966 : ((.push 248 (.fill 250)), d358937) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember967 : ((.push 248 (.fill 251)), d363235) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
theorem oracleMember968 : ((.push 248 (.fill 252)), d363819) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem oracleMember969 : ((.push 248 (.fill 253)), d364421) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
theorem oracleMember970 : ((.push 248 (.fill 254)), d364965) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
theorem oracleMember971 : ((.push 248 (.fill 255)), d365448) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
theorem oracleMember972 : ((.push 248 (.fill 256)), d365809) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
theorem oracleMember973 : ((.push 248 (.fill 257)), d366034) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
theorem oracleMember974 : ((.push 248 (.fill 258)), d366084) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))
theorem oracleMember975 : ((.push 248 (.fill 259)), d366139) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))
theorem oracleMember976 : ((.push 248 (.fill 260)), d366199) ∈ rowCases978 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))
noncomputable def rowCases979 : List OracleBranch := [((.walk 246), d271214), ((.push 246 (.stay 245)), d338652)]
theorem oracleMember977 : ((.walk 246), d271214) ∈ rowCases979 := by
  exact List.mem_cons_self
theorem oracleMember978 : ((.push 246 (.stay 245)), d338652) ∈ rowCases979 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases980 : List OracleBranch := [((.walk 226), d331335)]
theorem oracleMember979 : ((.walk 226), d331335) ∈ rowCases980 := by
  exact List.mem_cons_self
noncomputable def rowCases981 : List OracleBranch := [((.walk 224), d306035)]
theorem oracleMember980 : ((.walk 224), d306035) ∈ rowCases981 := by
  exact List.mem_cons_self
noncomputable def rowCases982 : List OracleBranch := []
noncomputable def rowCases983 : List OracleBranch := []
noncomputable def rowCases984 : List OracleBranch := [((.walk 226), d325306), ((.push 226 (.stay 204)), d271212)]
theorem oracleMember981 : ((.walk 226), d325306) ∈ rowCases984 := by
  exact List.mem_cons_self
theorem oracleMember982 : ((.push 226 (.stay 204)), d271212) ∈ rowCases984 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases985 : List OracleBranch := []
noncomputable def rowCases986 : List OracleBranch := [((.walk 249), d370801), ((.push 249 (.fill 250)), d370807), ((.push 249 (.stay 250)), d370936)]
theorem oracleMember983 : ((.walk 249), d370801) ∈ rowCases986 := by
  exact List.mem_cons_self
theorem oracleMember984 : ((.push 249 (.fill 250)), d370807) ∈ rowCases986 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember985 : ((.push 249 (.stay 250)), d370936) ∈ rowCases986 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases987 : List OracleBranch := [((.walk 247), d14), ((.push 247 (.stay 246)), d46864)]
theorem oracleMember986 : ((.walk 247), d14) ∈ rowCases987 := by
  exact List.mem_cons_self
theorem oracleMember987 : ((.push 247 (.stay 246)), d46864) ∈ rowCases987 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases988 : List OracleBranch := []
noncomputable def rowCases989 : List OracleBranch := [((.walk 225), d318725)]
theorem oracleMember988 : ((.walk 225), d318725) ∈ rowCases989 := by
  exact List.mem_cons_self
noncomputable def rowCases990 : List OracleBranch := []
noncomputable def rowCases991 : List OracleBranch := []
noncomputable def rowCases992 : List OracleBranch := []
noncomputable def rowCases993 : List OracleBranch := []
noncomputable def rowCases994 : List OracleBranch := [((.walk 250), d375596), ((.push 250 (.fill 251)), d375734), ((.push 250 (.stay 251)), d375866)]
theorem oracleMember989 : ((.walk 250), d375596) ∈ rowCases994 := by
  exact List.mem_cons_self
theorem oracleMember990 : ((.push 250 (.fill 251)), d375734) ∈ rowCases994 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem oracleMember991 : ((.push 250 (.stay 251)), d375866) ∈ rowCases994 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
noncomputable def rowCases995 : List OracleBranch := [((.walk 248), d370801), ((.push 248 (.stay 247)), d358929)]
theorem oracleMember992 : ((.walk 248), d370801) ∈ rowCases995 := by
  exact List.mem_cons_self
theorem oracleMember993 : ((.push 248 (.stay 247)), d358929) ∈ rowCases995 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases996 : List OracleBranch := []
noncomputable def rowCases997 : List OracleBranch := [((.walk 226), d331330)]
theorem oracleMember994 : ((.walk 226), d331330) ∈ rowCases997 := by
  exact List.mem_cons_self
noncomputable def rowCases998 : List OracleBranch := []
noncomputable def rowCases999 : List OracleBranch := []
end NetHack.Soko22Hazard87
