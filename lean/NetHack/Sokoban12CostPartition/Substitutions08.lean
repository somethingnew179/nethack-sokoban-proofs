/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub960 (p : Pattern) : d12 (change p 10000 (some 193)) = d924 p := by
  change (if p 168 then d11 (change p 10000 (some 193)) else d7 (change p 10000 (some 193))) = d924 p
  rw [sub959, sub948]
  rfl
theorem sub961 (p : Pattern) : d5 (change p 10000 (some 193)) = d5 p := by
  rfl
theorem sub962 (p : Pattern) : d58 (change p 10000 (some 193)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 193)) else d4 (change p 10000 (some 193))) = d58 p
  rw [sub961, sub949]
  rfl
theorem sub963 (p : Pattern) : d59 (change p 10000 (some 193)) = d58 p := by
  change d58 (change p 10000 (some 193)) = d58 p
  exact sub962 p
theorem sub964 (p : Pattern) : d60 (change p 10000 (some 193)) = d925 p := by
  change (if p 192 then d59 (change p 10000 (some 193)) else d9 (change p 10000 (some 193))) = d925 p
  rw [sub963, sub957]
  rfl
theorem sub965 (p : Pattern) : d61 (change p 10000 (some 193)) = d926 p := by
  change (if p 186 then d60 (change p 10000 (some 193)) else d11 (change p 10000 (some 193))) = d926 p
  rw [sub964, sub959]
  rfl
theorem sub966 (p : Pattern) : d62 (change p 10000 (some 193)) = d927 p := by
  change (if p 168 then d61 (change p 10000 (some 193)) else d56 (change p 10000 (some 193))) = d927 p
  rw [sub965, sub952]
  rfl
theorem sub967 (p : Pattern) : d63 (change p 10000 (some 193)) = d928 p := by
  change (if p 160 then d62 (change p 10000 (some 193)) else d12 (change p 10000 (some 193))) = d928 p
  rw [sub966, sub960]
  rfl
theorem sub968 (p : Pattern) : d64 (change p 10000 (some 193)) = d929 p := by
  change (if p 141 then d63 (change p 10000 (some 193)) else d57 (change p 10000 (some 193))) = d929 p
  rw [sub967, sub953]
  rfl
theorem sub969 (p : Pattern) : d106 (change p 10000 (some 193)) = d930 p := by
  change (if p 160 then d55 (change p 10000 (some 193)) else d7 (change p 10000 (some 193))) = d930 p
  rw [sub951, sub948]
  rfl
theorem sub970 (p : Pattern) : d119 (change p 10000 (some 193)) = d931 p := by
  change (if p 187 then d55 (change p 10000 (some 193)) else d7 (change p 10000 (some 193))) = d931 p
  rw [sub951, sub948]
  rfl
theorem sub971 (p : Pattern) : d120 (change p 10000 (some 193)) = d932 p := by
  change (if p 186 then d119 (change p 10000 (some 193)) else d7 (change p 10000 (some 193))) = d932 p
  rw [sub970, sub948]
  rfl
theorem sub972 (p : Pattern) : d121 (change p 10000 (some 193)) = d933 p := by
  change (if p 160 then d55 (change p 10000 (some 193)) else d120 (change p 10000 (some 193))) = d933 p
  rw [sub951, sub971]
  rfl
theorem sub973 (p : Pattern) : d122 (change p 10000 (some 193)) = d934 p := by
  change (if p 159 then d121 (change p 10000 (some 193)) else d106 (change p 10000 (some 193))) = d934 p
  rw [sub972, sub969]
  rfl
theorem sub974 (p : Pattern) : d179 (change p 10000 (some 193)) = d935 p := by
  change (if p 158 then d122 (change p 10000 (some 193)) else d106 (change p 10000 (some 193))) = d935 p
  rw [sub973, sub969]
  rfl
theorem sub975 (p : Pattern) : d65 (change p 10000 (some 193)) = d936 p := by
  change (if p 168 then d60 (change p 10000 (some 193)) else d55 (change p 10000 (some 193))) = d936 p
  rw [sub964, sub951]
  rfl
theorem sub976 (p : Pattern) : d109 (change p 10000 (some 193)) = d937 p := by
  change (if p 160 then d65 (change p 10000 (some 193)) else d12 (change p 10000 (some 193))) = d937 p
  rw [sub975, sub960]
  rfl
theorem sub977 (p : Pattern) : d125 (change p 10000 (some 193)) = d938 p := by
  change (if p 187 then d60 (change p 10000 (some 193)) else d11 (change p 10000 (some 193))) = d938 p
  rw [sub964, sub959]
  rfl
theorem sub978 (p : Pattern) : d126 (change p 10000 (some 193)) = d939 p := by
  change (if p 186 then d125 (change p 10000 (some 193)) else d11 (change p 10000 (some 193))) = d939 p
  rw [sub977, sub959]
  rfl
theorem sub979 (p : Pattern) : d127 (change p 10000 (some 193)) = d940 p := by
  change (if p 168 then d126 (change p 10000 (some 193)) else d120 (change p 10000 (some 193))) = d940 p
  rw [sub978, sub971]
  rfl
theorem sub980 (p : Pattern) : d128 (change p 10000 (some 193)) = d941 p := by
  change (if p 160 then d65 (change p 10000 (some 193)) else d127 (change p 10000 (some 193))) = d941 p
  rw [sub975, sub979]
  rfl
theorem sub981 (p : Pattern) : d129 (change p 10000 (some 193)) = d942 p := by
  change (if p 159 then d128 (change p 10000 (some 193)) else d109 (change p 10000 (some 193))) = d942 p
  rw [sub980, sub976]
  rfl
theorem sub982 (p : Pattern) : d237 (change p 10000 (some 193)) = d943 p := by
  change (if p 158 then d129 (change p 10000 (some 193)) else d109 (change p 10000 (some 193))) = d943 p
  rw [sub981, sub976]
  rfl
theorem sub983 (p : Pattern) : d238 (change p 10000 (some 193)) = d944 p := by
  change (if p 141 then d237 (change p 10000 (some 193)) else d179 (change p 10000 (some 193))) = d944 p
  rw [sub982, sub974]
  rfl
theorem sub984 (p : Pattern) : d239 (change p 10000 (some 193)) = d945 p := by
  change (if p 134 then d238 (change p 10000 (some 193)) else d64 (change p 10000 (some 193))) = d945 p
  rw [sub983, sub968]
  rfl
theorem sub985 (p : Pattern) : d68 (change p 10000 (some 193)) = d946 p := by
  change (if p 158 then d55 (change p 10000 (some 193)) else d57 (change p 10000 (some 193))) = d946 p
  rw [sub951, sub953]
  rfl
theorem sub986 (p : Pattern) : d69 (change p 10000 (some 193)) = d947 p := by
  change (if p 158 then d65 (change p 10000 (some 193)) else d63 (change p 10000 (some 193))) = d947 p
  rw [sub975, sub967]
  rfl
theorem sub987 (p : Pattern) : d70 (change p 10000 (some 193)) = d948 p := by
  change (if p 141 then d69 (change p 10000 (some 193)) else d68 (change p 10000 (some 193))) = d948 p
  rw [sub986, sub985]
  rfl
theorem sub988 (p : Pattern) : d181 (change p 10000 (some 193)) = d949 p := by
  change (if p 158 then d55 (change p 10000 (some 193)) else d122 (change p 10000 (some 193))) = d949 p
  rw [sub951, sub973]
  rfl
theorem sub989 (p : Pattern) : d240 (change p 10000 (some 193)) = d950 p := by
  change (if p 158 then d65 (change p 10000 (some 193)) else d129 (change p 10000 (some 193))) = d950 p
  rw [sub975, sub981]
  rfl
theorem sub990 (p : Pattern) : d241 (change p 10000 (some 193)) = d951 p := by
  change (if p 141 then d240 (change p 10000 (some 193)) else d181 (change p 10000 (some 193))) = d951 p
  rw [sub989, sub988]
  rfl
theorem sub991 (p : Pattern) : d242 (change p 10000 (some 193)) = d952 p := by
  change (if p 134 then d241 (change p 10000 (some 193)) else d70 (change p 10000 (some 193))) = d952 p
  rw [sub990, sub987]
  rfl
theorem sub992 (p : Pattern) : d243 (change p 10000 (some 193)) = d953 p := by
  change (if p 133 then d242 (change p 10000 (some 193)) else d239 (change p 10000 (some 193))) = d953 p
  rw [sub991, sub984]
  rfl
theorem sub993 (p : Pattern) : d66 (change p 10000 (some 193)) = d954 p := by
  change (if p 141 then d65 (change p 10000 (some 193)) else d55 (change p 10000 (some 193))) = d954 p
  rw [sub975, sub951]
  rfl
theorem sub994 (p : Pattern) : d244 (change p 10000 (some 193)) = d955 p := by
  change (if p 133 then d66 (change p 10000 (some 193)) else d242 (change p 10000 (some 193))) = d955 p
  rw [sub993, sub991]
  rfl
theorem sub995 (p : Pattern) : d245 (change p 10000 (some 193)) = d956 p := by
  change (if p 132 then d244 (change p 10000 (some 193)) else d243 (change p 10000 (some 193))) = d956 p
  rw [sub994, sub992]
  rfl
theorem sub996 (p : Pattern) : d137 (change p 10000 (some 193)) = d957 p := by
  change (if p 186 then d55 (change p 10000 (some 193)) else d119 (change p 10000 (some 193))) = d957 p
  rw [sub951, sub970]
  rfl
theorem sub997 (p : Pattern) : d139 (change p 10000 (some 193)) = d958 p := by
  change (if p 160 then d137 (change p 10000 (some 193)) else d120 (change p 10000 (some 193))) = d958 p
  rw [sub996, sub971]
  rfl
theorem sub998 (p : Pattern) : d153 (change p 10000 (some 193)) = d959 p := by
  change (if p 159 then d139 (change p 10000 (some 193)) else d57 (change p 10000 (some 193))) = d959 p
  rw [sub997, sub953]
  rfl
theorem sub999 (p : Pattern) : d186 (change p 10000 (some 193)) = d960 p := by
  change (if p 158 then d153 (change p 10000 (some 193)) else d57 (change p 10000 (some 193))) = d960 p
  rw [sub998, sub953]
  rfl
theorem sub1000 (p : Pattern) : d143 (change p 10000 (some 193)) = d961 p := by
  change (if p 186 then d60 (change p 10000 (some 193)) else d125 (change p 10000 (some 193))) = d961 p
  rw [sub964, sub977]
  rfl
theorem sub1001 (p : Pattern) : d144 (change p 10000 (some 193)) = d962 p := by
  change (if p 168 then d143 (change p 10000 (some 193)) else d137 (change p 10000 (some 193))) = d962 p
  rw [sub1000, sub996]
  rfl
theorem sub1002 (p : Pattern) : d146 (change p 10000 (some 193)) = d963 p := by
  change (if p 160 then d144 (change p 10000 (some 193)) else d127 (change p 10000 (some 193))) = d963 p
  rw [sub1001, sub979]
  rfl
theorem sub1003 (p : Pattern) : d155 (change p 10000 (some 193)) = d964 p := by
  change (if p 159 then d146 (change p 10000 (some 193)) else d63 (change p 10000 (some 193))) = d964 p
  rw [sub1002, sub967]
  rfl
theorem sub1004 (p : Pattern) : d246 (change p 10000 (some 193)) = d965 p := by
  change (if p 158 then d155 (change p 10000 (some 193)) else d63 (change p 10000 (some 193))) = d965 p
  rw [sub1003, sub967]
  rfl
theorem sub1005 (p : Pattern) : d247 (change p 10000 (some 193)) = d966 p := by
  change (if p 141 then d246 (change p 10000 (some 193)) else d186 (change p 10000 (some 193))) = d966 p
  rw [sub1004, sub999]
  rfl
theorem sub1006 (p : Pattern) : d248 (change p 10000 (some 193)) = d967 p := by
  change (if p 134 then d66 (change p 10000 (some 193)) else d247 (change p 10000 (some 193))) = d967 p
  rw [sub993, sub1005]
  rfl
theorem sub1007 (p : Pattern) : d138 (change p 10000 (some 193)) = d968 p := by
  change (if p 160 then d137 (change p 10000 (some 193)) else d7 (change p 10000 (some 193))) = d968 p
  rw [sub996, sub948]
  rfl
theorem sub1008 (p : Pattern) : d140 (change p 10000 (some 193)) = d969 p := by
  change (if p 159 then d139 (change p 10000 (some 193)) else d138 (change p 10000 (some 193))) = d969 p
  rw [sub997, sub1007]
  rfl
theorem sub1009 (p : Pattern) : d188 (change p 10000 (some 193)) = d970 p := by
  change (if p 158 then d55 (change p 10000 (some 193)) else d140 (change p 10000 (some 193))) = d970 p
  rw [sub951, sub1008]
  rfl
theorem sub1010 (p : Pattern) : d145 (change p 10000 (some 193)) = d971 p := by
  change (if p 160 then d144 (change p 10000 (some 193)) else d12 (change p 10000 (some 193))) = d971 p
  rw [sub1001, sub960]
  rfl
theorem sub1011 (p : Pattern) : d147 (change p 10000 (some 193)) = d972 p := by
  change (if p 159 then d146 (change p 10000 (some 193)) else d145 (change p 10000 (some 193))) = d972 p
  rw [sub1002, sub1010]
  rfl
theorem sub1012 (p : Pattern) : d249 (change p 10000 (some 193)) = d973 p := by
  change (if p 158 then d65 (change p 10000 (some 193)) else d147 (change p 10000 (some 193))) = d973 p
  rw [sub975, sub1011]
  rfl
theorem sub1013 (p : Pattern) : d250 (change p 10000 (some 193)) = d974 p := by
  change (if p 141 then d249 (change p 10000 (some 193)) else d188 (change p 10000 (some 193))) = d974 p
  rw [sub1012, sub1009]
  rfl
theorem sub1014 (p : Pattern) : d251 (change p 10000 (some 193)) = d975 p := by
  change (if p 134 then d66 (change p 10000 (some 193)) else d250 (change p 10000 (some 193))) = d975 p
  rw [sub993, sub1013]
  rfl
theorem sub1015 (p : Pattern) : d252 (change p 10000 (some 193)) = d976 p := by
  change (if p 133 then d251 (change p 10000 (some 193)) else d248 (change p 10000 (some 193))) = d976 p
  rw [sub1014, sub1006]
  rfl
theorem sub1016 (p : Pattern) : d191 (change p 10000 (some 193)) = d977 p := by
  change (if p 158 then d55 (change p 10000 (some 193)) else d153 (change p 10000 (some 193))) = d977 p
  rw [sub951, sub998]
  rfl
theorem sub1017 (p : Pattern) : d253 (change p 10000 (some 193)) = d978 p := by
  change (if p 158 then d65 (change p 10000 (some 193)) else d155 (change p 10000 (some 193))) = d978 p
  rw [sub975, sub1003]
  rfl
theorem sub1018 (p : Pattern) : d254 (change p 10000 (some 193)) = d979 p := by
  change (if p 141 then d253 (change p 10000 (some 193)) else d191 (change p 10000 (some 193))) = d979 p
  rw [sub1017, sub1016]
  rfl
theorem sub1019 (p : Pattern) : d255 (change p 10000 (some 193)) = d980 p := by
  change (if p 134 then d66 (change p 10000 (some 193)) else d254 (change p 10000 (some 193))) = d980 p
  rw [sub993, sub1018]
  rfl
theorem sub1020 (p : Pattern) : d256 (change p 10000 (some 193)) = d981 p := by
  change (if p 133 then d66 (change p 10000 (some 193)) else d255 (change p 10000 (some 193))) = d981 p
  rw [sub993, sub1019]
  rfl
theorem sub1021 (p : Pattern) : d257 (change p 10000 (some 193)) = d982 p := by
  change (if p 132 then d256 (change p 10000 (some 193)) else d252 (change p 10000 (some 193))) = d982 p
  rw [sub1020, sub1015]
  rfl
theorem sub1022 (p : Pattern) : d258 (change p 10000 (some 193)) = d983 p := by
  change (if p 108 then d257 (change p 10000 (some 193)) else d245 (change p 10000 (some 193))) = d983 p
  rw [sub1021, sub995]
  rfl
theorem sub1023 (p : Pattern) : d0 (change p 168 none) = d0 p := by
  rfl
theorem sub1024 (p : Pattern) : d2 (change p 168 none) = d2 p := by
  rfl
theorem sub1025 (p : Pattern) : d6 (change p 168 none) = d6 p := by
  change (if p 193 then d2 (change p 168 none) else d0 (change p 168 none)) = d6 p
  rw [sub1024, sub1023]
  rfl
theorem sub1026 (p : Pattern) : d7 (change p 168 none) = d7 p := by
  change (if p 192 then d6 (change p 168 none) else d0 (change p 168 none)) = d7 p
  rw [sub1025, sub1023]
  rfl
theorem sub1027 (p : Pattern) : d21 (change p 168 none) = d7 p := by
  change d7 (change p 168 none) = d7 p
  exact sub1026 p
theorem sub1028 (p : Pattern) : d4 (change p 168 none) = d4 p := by
  rfl
theorem sub1029 (p : Pattern) : d54 (change p 168 none) = d54 p := by
  change (if p 193 then d4 (change p 168 none) else d2 (change p 168 none)) = d54 p
  rw [sub1028, sub1024]
  rfl
theorem sub1030 (p : Pattern) : d55 (change p 168 none) = d55 p := by
  change (if p 192 then d54 (change p 168 none) else d2 (change p 168 none)) = d55 p
  rw [sub1029, sub1024]
  rfl
theorem sub1031 (p : Pattern) : d56 (change p 168 none) = d56 p := by
  change (if p 186 then d55 (change p 168 none) else d7 (change p 168 none)) = d56 p
  rw [sub1030, sub1026]
  rfl
theorem sub1032 (p : Pattern) : d375 (change p 168 none) = d56 p := by
  change d56 (change p 168 none) = d56 p
  exact sub1031 p
theorem sub1033 (p : Pattern) : d376 (change p 168 none) = d57 p := by
  change (if p 160 then d375 (change p 168 none) else d21 (change p 168 none)) = d57 p
  rw [sub1032, sub1027]
  rfl
theorem sub1034 (p : Pattern) : d22 (change p 168 none) = d7 p := by
  change d7 (change p 168 none) = d7 p
  exact sub1026 p
theorem sub1035 (p : Pattern) : d377 (change p 168 none) = d56 p := by
  change d56 (change p 168 none) = d56 p
  exact sub1031 p
theorem sub1036 (p : Pattern) : d378 (change p 168 none) = d57 p := by
  change (if p 160 then d377 (change p 168 none) else d22 (change p 168 none)) = d57 p
  rw [sub1035, sub1034]
  rfl
theorem sub1037 (p : Pattern) : d379 (change p 168 none) = d57 p := by
  change (if p 141 then d378 (change p 168 none) else d376 (change p 168 none)) = d57 p
  rw [sub1036, sub1033]
  simp only [ite_self]
theorem sub1038 (p : Pattern) : d380 (change p 168 none) = d55 p := by
  change d55 (change p 168 none) = d55 p
  exact sub1030 p
theorem sub1039 (p : Pattern) : d381 (change p 168 none) = d106 p := by
  change (if p 160 then d380 (change p 168 none) else d21 (change p 168 none)) = d106 p
  rw [sub1038, sub1027]
  rfl
theorem sub1040 (p : Pattern) : d119 (change p 168 none) = d119 p := by
  change (if p 187 then d55 (change p 168 none) else d7 (change p 168 none)) = d119 p
  rw [sub1030, sub1026]
  rfl
theorem sub1041 (p : Pattern) : d120 (change p 168 none) = d120 p := by
  change (if p 186 then d119 (change p 168 none) else d7 (change p 168 none)) = d120 p
  rw [sub1040, sub1026]
  rfl
theorem sub1042 (p : Pattern) : d382 (change p 168 none) = d120 p := by
  change d120 (change p 168 none) = d120 p
  exact sub1041 p
theorem sub1043 (p : Pattern) : d383 (change p 168 none) = d121 p := by
  change (if p 160 then d380 (change p 168 none) else d382 (change p 168 none)) = d121 p
  rw [sub1038, sub1042]
  rfl
theorem sub1044 (p : Pattern) : d384 (change p 168 none) = d122 p := by
  change (if p 159 then d383 (change p 168 none) else d381 (change p 168 none)) = d122 p
  rw [sub1043, sub1039]
  rfl
theorem sub1045 (p : Pattern) : d385 (change p 168 none) = d179 p := by
  change (if p 158 then d384 (change p 168 none) else d381 (change p 168 none)) = d179 p
  rw [sub1044, sub1039]
  rfl
theorem sub1046 (p : Pattern) : d386 (change p 168 none) = d55 p := by
  change d55 (change p 168 none) = d55 p
  exact sub1030 p
theorem sub1047 (p : Pattern) : d387 (change p 168 none) = d106 p := by
  change (if p 160 then d386 (change p 168 none) else d22 (change p 168 none)) = d106 p
  rw [sub1046, sub1034]
  rfl
theorem sub1048 (p : Pattern) : d388 (change p 168 none) = d120 p := by
  change d120 (change p 168 none) = d120 p
  exact sub1041 p
theorem sub1049 (p : Pattern) : d389 (change p 168 none) = d121 p := by
  change (if p 160 then d386 (change p 168 none) else d388 (change p 168 none)) = d121 p
  rw [sub1046, sub1048]
  rfl
theorem sub1050 (p : Pattern) : d390 (change p 168 none) = d122 p := by
  change (if p 159 then d389 (change p 168 none) else d387 (change p 168 none)) = d122 p
  rw [sub1049, sub1047]
  rfl
theorem sub1051 (p : Pattern) : d391 (change p 168 none) = d179 p := by
  change (if p 158 then d390 (change p 168 none) else d387 (change p 168 none)) = d179 p
  rw [sub1050, sub1047]
  rfl
theorem sub1052 (p : Pattern) : d392 (change p 168 none) = d179 p := by
  change (if p 141 then d391 (change p 168 none) else d385 (change p 168 none)) = d179 p
  rw [sub1051, sub1045]
  simp only [ite_self]
theorem sub1053 (p : Pattern) : d393 (change p 168 none) = d180 p := by
  change (if p 134 then d392 (change p 168 none) else d379 (change p 168 none)) = d180 p
  rw [sub1052, sub1037]
  rfl
theorem sub1054 (p : Pattern) : d394 (change p 168 none) = d68 p := by
  change (if p 158 then d380 (change p 168 none) else d376 (change p 168 none)) = d68 p
  rw [sub1038, sub1033]
  rfl
theorem sub1055 (p : Pattern) : d395 (change p 168 none) = d68 p := by
  change (if p 158 then d386 (change p 168 none) else d378 (change p 168 none)) = d68 p
  rw [sub1046, sub1036]
  rfl
theorem sub1056 (p : Pattern) : d396 (change p 168 none) = d68 p := by
  change (if p 141 then d395 (change p 168 none) else d394 (change p 168 none)) = d68 p
  rw [sub1055, sub1054]
  simp only [ite_self]
theorem sub1057 (p : Pattern) : d397 (change p 168 none) = d181 p := by
  change (if p 158 then d380 (change p 168 none) else d384 (change p 168 none)) = d181 p
  rw [sub1038, sub1044]
  rfl
theorem sub1058 (p : Pattern) : d398 (change p 168 none) = d181 p := by
  change (if p 158 then d386 (change p 168 none) else d390 (change p 168 none)) = d181 p
  rw [sub1046, sub1050]
  rfl
theorem sub1059 (p : Pattern) : d399 (change p 168 none) = d181 p := by
  change (if p 141 then d398 (change p 168 none) else d397 (change p 168 none)) = d181 p
  rw [sub1058, sub1057]
  simp only [ite_self]
theorem sub1060 (p : Pattern) : d400 (change p 168 none) = d182 p := by
  change (if p 134 then d399 (change p 168 none) else d396 (change p 168 none)) = d182 p
  rw [sub1059, sub1056]
  rfl
theorem sub1061 (p : Pattern) : d401 (change p 168 none) = d183 p := by
  change (if p 133 then d400 (change p 168 none) else d393 (change p 168 none)) = d183 p
  rw [sub1060, sub1053]
  rfl
theorem sub1062 (p : Pattern) : d402 (change p 168 none) = d55 p := by
  change (if p 141 then d386 (change p 168 none) else d380 (change p 168 none)) = d55 p
  rw [sub1046, sub1038]
  simp only [ite_self]
theorem sub1063 (p : Pattern) : d403 (change p 168 none) = d184 p := by
  change (if p 133 then d402 (change p 168 none) else d400 (change p 168 none)) = d184 p
  rw [sub1062, sub1060]
  rfl
theorem sub1064 (p : Pattern) : d404 (change p 168 none) = d185 p := by
  change (if p 132 then d403 (change p 168 none) else d401 (change p 168 none)) = d185 p
  rw [sub1063, sub1061]
  rfl
theorem sub1065 (p : Pattern) : d137 (change p 168 none) = d137 p := by
  change (if p 186 then d55 (change p 168 none) else d119 (change p 168 none)) = d137 p
  rw [sub1030, sub1040]
  rfl
theorem sub1066 (p : Pattern) : d405 (change p 168 none) = d137 p := by
  change d137 (change p 168 none) = d137 p
  exact sub1065 p
theorem sub1067 (p : Pattern) : d406 (change p 168 none) = d139 p := by
  change (if p 160 then d405 (change p 168 none) else d382 (change p 168 none)) = d139 p
  rw [sub1066, sub1042]
  rfl
theorem sub1068 (p : Pattern) : d407 (change p 168 none) = d153 p := by
  change (if p 159 then d406 (change p 168 none) else d376 (change p 168 none)) = d153 p
  rw [sub1067, sub1033]
  rfl
theorem sub1069 (p : Pattern) : d408 (change p 168 none) = d186 p := by
  change (if p 158 then d407 (change p 168 none) else d376 (change p 168 none)) = d186 p
  rw [sub1068, sub1033]
  rfl
theorem sub1070 (p : Pattern) : d409 (change p 168 none) = d137 p := by
  change d137 (change p 168 none) = d137 p
  exact sub1065 p
theorem sub1071 (p : Pattern) : d410 (change p 168 none) = d139 p := by
  change (if p 160 then d409 (change p 168 none) else d388 (change p 168 none)) = d139 p
  rw [sub1070, sub1048]
  rfl
theorem sub1072 (p : Pattern) : d411 (change p 168 none) = d153 p := by
  change (if p 159 then d410 (change p 168 none) else d378 (change p 168 none)) = d153 p
  rw [sub1071, sub1036]
  rfl
theorem sub1073 (p : Pattern) : d412 (change p 168 none) = d186 p := by
  change (if p 158 then d411 (change p 168 none) else d378 (change p 168 none)) = d186 p
  rw [sub1072, sub1036]
  rfl
theorem sub1074 (p : Pattern) : d413 (change p 168 none) = d186 p := by
  change (if p 141 then d412 (change p 168 none) else d408 (change p 168 none)) = d186 p
  rw [sub1073, sub1069]
  simp only [ite_self]
theorem sub1075 (p : Pattern) : d414 (change p 168 none) = d187 p := by
  change (if p 134 then d402 (change p 168 none) else d413 (change p 168 none)) = d187 p
  rw [sub1062, sub1074]
  rfl
theorem sub1076 (p : Pattern) : d415 (change p 168 none) = d138 p := by
  change (if p 160 then d405 (change p 168 none) else d21 (change p 168 none)) = d138 p
  rw [sub1066, sub1027]
  rfl
theorem sub1077 (p : Pattern) : d416 (change p 168 none) = d140 p := by
  change (if p 159 then d406 (change p 168 none) else d415 (change p 168 none)) = d140 p
  rw [sub1067, sub1076]
  rfl
theorem sub1078 (p : Pattern) : d417 (change p 168 none) = d188 p := by
  change (if p 158 then d380 (change p 168 none) else d416 (change p 168 none)) = d188 p
  rw [sub1038, sub1077]
  rfl
theorem sub1079 (p : Pattern) : d418 (change p 168 none) = d138 p := by
  change (if p 160 then d409 (change p 168 none) else d22 (change p 168 none)) = d138 p
  rw [sub1070, sub1034]
  rfl
end NetHack.Sokoban12CostPartition
