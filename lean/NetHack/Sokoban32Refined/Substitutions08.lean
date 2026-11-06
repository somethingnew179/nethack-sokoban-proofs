/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub960 (p : Pattern) : d63 (change p 10000 (some 161)) = d1006 p := by
  change (if p 134 then d55 (change p 10000 (some 161)) else d62 (change p 10000 (some 161))) = d1006 p
  rw [sub952, sub959]
  rfl
theorem sub961 (p : Pattern) : d64 (change p 10000 (some 161)) = d1011 p := by
  change (if p 133 then d63 (change p 10000 (some 161)) else d60 (change p 10000 (some 161))) = d1011 p
  rw [sub960, sub957]
  rfl
theorem sub962 (p : Pattern) : d65 (change p 10000 (some 161)) = d1012 p := by
  change (if p 132 then d64 (change p 10000 (some 161)) else d57 (change p 10000 (some 161))) = d1012 p
  rw [sub961, sub954]
  rfl
theorem sub963 (p : Pattern) : d66 (change p 10000 (some 161)) = d1013 p := by
  change (if p 113 then d65 (change p 10000 (some 161)) else d51 (change p 10000 (some 161))) = d1013 p
  rw [sub962, sub948]
  rfl
theorem sub964 (p : Pattern) : d67 (change p 10000 (some 161)) = d1014 p := by
  change (if p 112 then d66 (change p 10000 (some 161)) else d45 (change p 10000 (some 161))) = d1014 p
  rw [sub963, sub942]
  rfl
theorem sub965 (p : Pattern) : d68 (change p 10000 (some 161)) = d705 p := by
  change (if p 139 then d2 (change p 10000 (some 161)) else d40 (change p 10000 (some 161))) = d705 p
  rw [sub898, sub937]
  rfl
theorem sub966 (p : Pattern) : d69 (change p 10000 (some 161)) = d706 p := by
  change (if p 138 then d68 (change p 10000 (some 161)) else d40 (change p 10000 (some 161))) = d706 p
  rw [sub965, sub937]
  rfl
theorem sub967 (p : Pattern) : d70 (change p 10000 (some 161)) = d1015 p := by
  change (if p 139 then d2 (change p 10000 (some 161)) else d24 (change p 10000 (some 161))) = d1015 p
  rw [sub898, sub921]
  rfl
theorem sub968 (p : Pattern) : d71 (change p 10000 (some 161)) = d1016 p := by
  change (if p 138 then d70 (change p 10000 (some 161)) else d24 (change p 10000 (some 161))) = d1016 p
  rw [sub967, sub921]
  rfl
theorem sub969 (p : Pattern) : d72 (change p 10000 (some 161)) = d1017 p := by
  change (if p 134 then d71 (change p 10000 (some 161)) else d69 (change p 10000 (some 161))) = d1017 p
  rw [sub968, sub966]
  rfl
theorem sub970 (p : Pattern) : d73 (change p 10000 (some 161)) = d1018 p := by
  change (if p 133 then d72 (change p 10000 (some 161)) else d27 (change p 10000 (some 161))) = d1018 p
  rw [sub969, sub924]
  rfl
theorem sub971 (p : Pattern) : d74 (change p 10000 (some 161)) = d1019 p := by
  change (if p 132 then d73 (change p 10000 (some 161)) else d28 (change p 10000 (some 161))) = d1019 p
  rw [sub970, sub925]
  rfl
theorem sub972 (p : Pattern) : d75 (change p 10000 (some 161)) = d1020 p := by
  change (if p 134 then d70 (change p 10000 (some 161)) else d68 (change p 10000 (some 161))) = d1020 p
  rw [sub967, sub965]
  rfl
theorem sub973 (p : Pattern) : d76 (change p 10000 (some 161)) = d1021 p := by
  change (if p 133 then d75 (change p 10000 (some 161)) else d27 (change p 10000 (some 161))) = d1021 p
  rw [sub972, sub924]
  rfl
theorem sub974 (p : Pattern) : d77 (change p 10000 (some 161)) = d1022 p := by
  change (if p 132 then d76 (change p 10000 (some 161)) else d28 (change p 10000 (some 161))) = d1022 p
  rw [sub973, sub925]
  rfl
theorem sub975 (p : Pattern) : d78 (change p 10000 (some 161)) = d1023 p := by
  change (if p 113 then d77 (change p 10000 (some 161)) else d74 (change p 10000 (some 161))) = d1023 p
  rw [sub974, sub971]
  rfl
theorem sub976 (p : Pattern) : d79 (change p 10000 (some 161)) = d1024 p := by
  change (if p 133 then d75 (change p 10000 (some 161)) else d46 (change p 10000 (some 161))) = d1024 p
  rw [sub972, sub943]
  rfl
theorem sub977 (p : Pattern) : d80 (change p 10000 (some 161)) = d1025 p := by
  change (if p 132 then d79 (change p 10000 (some 161)) else d47 (change p 10000 (some 161))) = d1025 p
  rw [sub976, sub944]
  rfl
theorem sub978 (p : Pattern) : d81 (change p 10000 (some 161)) = d1026 p := by
  change (if p 133 then d75 (change p 10000 (some 161)) else d56 (change p 10000 (some 161))) = d1026 p
  rw [sub972, sub953]
  rfl
theorem sub979 (p : Pattern) : d82 (change p 10000 (some 161)) = d1027 p := by
  change (if p 132 then d81 (change p 10000 (some 161)) else d57 (change p 10000 (some 161))) = d1027 p
  rw [sub978, sub954]
  rfl
theorem sub980 (p : Pattern) : d83 (change p 10000 (some 161)) = d1028 p := by
  change (if p 113 then d82 (change p 10000 (some 161)) else d80 (change p 10000 (some 161))) = d1028 p
  rw [sub979, sub977]
  rfl
theorem sub981 (p : Pattern) : d84 (change p 10000 (some 161)) = d1029 p := by
  change (if p 112 then d83 (change p 10000 (some 161)) else d78 (change p 10000 (some 161))) = d1029 p
  rw [sub980, sub975]
  rfl
theorem sub982 (p : Pattern) : d85 (change p 10000 (some 161)) = d1030 p := by
  change (if p 106 then d84 (change p 10000 (some 161)) else d67 (change p 10000 (some 161))) = d1030 p
  rw [sub981, sub964]
  rfl
theorem sub983 (p : Pattern) : d86 (change p 10000 (some 161)) = d719 p := by
  change (if p 138 then d52 (change p 10000 (some 161)) else d8 (change p 10000 (some 161))) = d719 p
  rw [sub949, sub904]
  rfl
theorem sub984 (p : Pattern) : d87 (change p 10000 (some 161)) = d1031 p := by
  change (if p 138 then d54 (change p 10000 (some 161)) else d20 (change p 10000 (some 161))) = d1031 p
  rw [sub951, sub917]
  rfl
theorem sub985 (p : Pattern) : d88 (change p 10000 (some 161)) = d1032 p := by
  change (if p 134 then d87 (change p 10000 (some 161)) else d86 (change p 10000 (some 161))) = d1032 p
  rw [sub984, sub983]
  rfl
theorem sub986 (p : Pattern) : d89 (change p 10000 (some 161)) = d1033 p := by
  change (if p 133 then d88 (change p 10000 (some 161)) else d86 (change p 10000 (some 161))) = d1033 p
  rw [sub985, sub983]
  rfl
theorem sub987 (p : Pattern) : d90 (change p 10000 (some 161)) = d1034 p := by
  change (if p 138 then d58 (change p 10000 (some 161)) else d33 (change p 10000 (some 161))) = d1034 p
  rw [sub955, sub930]
  rfl
theorem sub988 (p : Pattern) : d91 (change p 10000 (some 161)) = d1035 p := by
  change (if p 134 then d90 (change p 10000 (some 161)) else d86 (change p 10000 (some 161))) = d1035 p
  rw [sub987, sub983]
  rfl
theorem sub989 (p : Pattern) : d92 (change p 10000 (some 161)) = d719 p := by
  change (if p 138 then d61 (change p 10000 (some 161)) else d38 (change p 10000 (some 161))) = d719 p
  rw [sub958, sub935]
  rfl
theorem sub990 (p : Pattern) : d93 (change p 10000 (some 161)) = d1032 p := by
  change (if p 134 then d87 (change p 10000 (some 161)) else d92 (change p 10000 (some 161))) = d1032 p
  rw [sub984, sub989]
  rfl
theorem sub991 (p : Pattern) : d94 (change p 10000 (some 161)) = d1036 p := by
  change (if p 133 then d93 (change p 10000 (some 161)) else d91 (change p 10000 (some 161))) = d1036 p
  rw [sub990, sub988]
  rfl
theorem sub992 (p : Pattern) : d95 (change p 10000 (some 161)) = d1037 p := by
  change (if p 132 then d94 (change p 10000 (some 161)) else d89 (change p 10000 (some 161))) = d1037 p
  rw [sub991, sub986]
  rfl
theorem sub993 (p : Pattern) : d96 (change p 10000 (some 161)) = d1038 p := by
  change (if p 113 then d95 (change p 10000 (some 161)) else d45 (change p 10000 (some 161))) = d1038 p
  rw [sub992, sub942]
  rfl
theorem sub994 (p : Pattern) : d97 (change p 10000 (some 161)) = d705 p := by
  change (if p 139 then d2 (change p 10000 (some 161)) else d14 (change p 10000 (some 161))) = d705 p
  rw [sub898, sub911]
  rfl
theorem sub995 (p : Pattern) : d98 (change p 10000 (some 161)) = d706 p := by
  change (if p 138 then d97 (change p 10000 (some 161)) else d14 (change p 10000 (some 161))) = d706 p
  rw [sub994, sub911]
  rfl
theorem sub996 (p : Pattern) : d99 (change p 10000 (some 161)) = d1017 p := by
  change (if p 134 then d71 (change p 10000 (some 161)) else d98 (change p 10000 (some 161))) = d1017 p
  rw [sub968, sub995]
  rfl
theorem sub997 (p : Pattern) : d100 (change p 10000 (some 161)) = d1039 p := by
  change (if p 133 then d99 (change p 10000 (some 161)) else d98 (change p 10000 (some 161))) = d1039 p
  rw [sub996, sub995]
  rfl
theorem sub998 (p : Pattern) : d101 (change p 10000 (some 161)) = d1017 p := by
  change (if p 133 then d72 (change p 10000 (some 161)) else d99 (change p 10000 (some 161))) = d1017 p
  rw [sub969, sub996]
  simp only [ite_self]
theorem sub999 (p : Pattern) : d102 (change p 10000 (some 161)) = d1040 p := by
  change (if p 132 then d101 (change p 10000 (some 161)) else d100 (change p 10000 (some 161))) = d1040 p
  rw [sub998, sub997]
  rfl
theorem sub1000 (p : Pattern) : d103 (change p 10000 (some 161)) = d1041 p := by
  change (if p 112 then d102 (change p 10000 (some 161)) else d96 (change p 10000 (some 161))) = d1041 p
  rw [sub999, sub993]
  rfl
theorem sub1001 (p : Pattern) : d104 (change p 10000 (some 161)) = d1042 p := by
  change (if p 133 then d75 (change p 10000 (some 161)) else d88 (change p 10000 (some 161))) = d1042 p
  rw [sub972, sub985]
  rfl
theorem sub1002 (p : Pattern) : d105 (change p 10000 (some 161)) = d1043 p := by
  change (if p 132 then d104 (change p 10000 (some 161)) else d89 (change p 10000 (some 161))) = d1043 p
  rw [sub1001, sub986]
  rfl
theorem sub1003 (p : Pattern) : d106 (change p 10000 (some 161)) = d1044 p := by
  change (if p 113 then d105 (change p 10000 (some 161)) else d77 (change p 10000 (some 161))) = d1044 p
  rw [sub1002, sub974]
  rfl
theorem sub1004 (p : Pattern) : d107 (change p 10000 (some 161)) = d1045 p := by
  change (if p 133 then d2 (change p 10000 (some 161)) else d99 (change p 10000 (some 161))) = d1045 p
  rw [sub898, sub996]
  rfl
theorem sub1005 (p : Pattern) : d108 (change p 10000 (some 161)) = d1046 p := by
  change (if p 132 then d107 (change p 10000 (some 161)) else d100 (change p 10000 (some 161))) = d1046 p
  rw [sub1004, sub997]
  rfl
theorem sub1006 (p : Pattern) : d109 (change p 10000 (some 161)) = d1020 p := by
  change (if p 134 then d70 (change p 10000 (some 161)) else d97 (change p 10000 (some 161))) = d1020 p
  rw [sub967, sub994]
  rfl
theorem sub1007 (p : Pattern) : d110 (change p 10000 (some 161)) = d1047 p := by
  change (if p 133 then d109 (change p 10000 (some 161)) else d97 (change p 10000 (some 161))) = d1047 p
  rw [sub1006, sub994]
  rfl
theorem sub1008 (p : Pattern) : d111 (change p 10000 (some 161)) = d1048 p := by
  change (if p 133 then d2 (change p 10000 (some 161)) else d109 (change p 10000 (some 161))) = d1048 p
  rw [sub898, sub1006]
  rfl
theorem sub1009 (p : Pattern) : d112 (change p 10000 (some 161)) = d1049 p := by
  change (if p 132 then d111 (change p 10000 (some 161)) else d110 (change p 10000 (some 161))) = d1049 p
  rw [sub1008, sub1007]
  rfl
theorem sub1010 (p : Pattern) : d113 (change p 10000 (some 161)) = d1050 p := by
  change (if p 113 then d112 (change p 10000 (some 161)) else d108 (change p 10000 (some 161))) = d1050 p
  rw [sub1009, sub1005]
  rfl
theorem sub1011 (p : Pattern) : d114 (change p 10000 (some 161)) = d1051 p := by
  change (if p 112 then d113 (change p 10000 (some 161)) else d106 (change p 10000 (some 161))) = d1051 p
  rw [sub1010, sub1003]
  rfl
theorem sub1012 (p : Pattern) : d115 (change p 10000 (some 161)) = d1052 p := by
  change (if p 106 then d114 (change p 10000 (some 161)) else d103 (change p 10000 (some 161))) = d1052 p
  rw [sub1011, sub1000]
  rfl
theorem sub1013 (p : Pattern) : d116 (change p 10000 (some 161)) = d1053 p := by
  change (if p 86 then d115 (change p 10000 (some 161)) else d85 (change p 10000 (some 161))) = d1053 p
  rw [sub1012, sub982]
  rfl
theorem sub1014 (p : Pattern) : d117 (change p 10000 (some 161)) = d1054 p := by
  change (if p 112 then d83 (change p 10000 (some 161)) else d77 (change p 10000 (some 161))) = d1054 p
  rw [sub980, sub974]
  rfl
theorem sub1015 (p : Pattern) : d118 (change p 10000 (some 161)) = d1055 p := by
  change (if p 106 then d117 (change p 10000 (some 161)) else d67 (change p 10000 (some 161))) = d1055 p
  rw [sub1014, sub964]
  rfl
theorem sub1016 (p : Pattern) : d119 (change p 10000 (some 161)) = d1056 p := by
  change (if p 139 then d20 (change p 10000 (some 161)) else d33 (change p 10000 (some 161))) = d1056 p
  rw [sub917, sub930]
  rfl
theorem sub1017 (p : Pattern) : d120 (change p 10000 (some 161)) = d1057 p := by
  change (if p 138 then d58 (change p 10000 (some 161)) else d119 (change p 10000 (some 161))) = d1057 p
  rw [sub955, sub1016]
  rfl
theorem sub1018 (p : Pattern) : d121 (change p 10000 (some 161)) = d1058 p := by
  change (if p 134 then d120 (change p 10000 (some 161)) else d86 (change p 10000 (some 161))) = d1058 p
  rw [sub1017, sub983]
  rfl
theorem sub1019 (p : Pattern) : d122 (change p 10000 (some 161)) = d1059 p := by
  change (if p 133 then d93 (change p 10000 (some 161)) else d121 (change p 10000 (some 161))) = d1059 p
  rw [sub990, sub1018]
  rfl
theorem sub1020 (p : Pattern) : d123 (change p 10000 (some 161)) = d1060 p := by
  change (if p 132 then d122 (change p 10000 (some 161)) else d89 (change p 10000 (some 161))) = d1060 p
  rw [sub1019, sub986]
  rfl
theorem sub1021 (p : Pattern) : d124 (change p 10000 (some 161)) = d1061 p := by
  change (if p 113 then d123 (change p 10000 (some 161)) else d45 (change p 10000 (some 161))) = d1061 p
  rw [sub1020, sub942]
  rfl
theorem sub1022 (p : Pattern) : d125 (change p 10000 (some 161)) = d1020 p := by
  change (if p 133 then d75 (change p 10000 (some 161)) else d109 (change p 10000 (some 161))) = d1020 p
  rw [sub972, sub1006]
  simp only [ite_self]
theorem sub1023 (p : Pattern) : d126 (change p 10000 (some 161)) = d1062 p := by
  change (if p 132 then d125 (change p 10000 (some 161)) else d110 (change p 10000 (some 161))) = d1062 p
  rw [sub1022, sub1007]
  rfl
theorem sub1024 (p : Pattern) : d127 (change p 10000 (some 161)) = d1063 p := by
  change (if p 113 then d126 (change p 10000 (some 161)) else d102 (change p 10000 (some 161))) = d1063 p
  rw [sub1023, sub999]
  rfl
theorem sub1025 (p : Pattern) : d128 (change p 10000 (some 161)) = d1064 p := by
  change (if p 112 then d127 (change p 10000 (some 161)) else d124 (change p 10000 (some 161))) = d1064 p
  rw [sub1024, sub1021]
  rfl
theorem sub1026 (p : Pattern) : d129 (change p 10000 (some 161)) = d1065 p := by
  change (if p 113 then d82 (change p 10000 (some 161)) else d77 (change p 10000 (some 161))) = d1065 p
  rw [sub979, sub974]
  rfl
theorem sub1027 (p : Pattern) : d130 (change p 10000 (some 161)) = d1066 p := by
  change (if p 113 then d2 (change p 10000 (some 161)) else d112 (change p 10000 (some 161))) = d1066 p
  rw [sub898, sub1009]
  rfl
theorem sub1028 (p : Pattern) : d131 (change p 10000 (some 161)) = d1067 p := by
  change (if p 112 then d130 (change p 10000 (some 161)) else d129 (change p 10000 (some 161))) = d1067 p
  rw [sub1027, sub1026]
  rfl
theorem sub1029 (p : Pattern) : d132 (change p 10000 (some 161)) = d1068 p := by
  change (if p 106 then d131 (change p 10000 (some 161)) else d128 (change p 10000 (some 161))) = d1068 p
  rw [sub1028, sub1025]
  rfl
theorem sub1030 (p : Pattern) : d133 (change p 10000 (some 161)) = d1069 p := by
  change (if p 86 then d132 (change p 10000 (some 161)) else d118 (change p 10000 (some 161))) = d1069 p
  rw [sub1029, sub1015]
  rfl
theorem sub1031 (p : Pattern) : d134 (change p 10000 (some 161)) = d1070 p := by
  change (if p 80 then d133 (change p 10000 (some 161)) else d116 (change p 10000 (some 161))) = d1070 p
  rw [sub1030, sub1013]
  rfl
theorem sub1032 (p : Pattern) : d0 (change p 86 none) = d0 p := by
  rfl
theorem sub1033 (p : Pattern) : d2 (change p 86 none) = d2 p := by
  rfl
theorem sub1034 (p : Pattern) : d3 (change p 86 none) = d3 p := by
  change (if p 161 then d2 (change p 86 none) else d0 (change p 86 none)) = d3 p
  rw [sub1033, sub1032]
  rfl
theorem sub1035 (p : Pattern) : d4 (change p 86 none) = d4 p := by
  change (if p 160 then d3 (change p 86 none) else d0 (change p 86 none)) = d4 p
  rw [sub1034, sub1032]
  rfl
theorem sub1036 (p : Pattern) : d5 (change p 86 none) = d5 p := by
  change (if p 160 then d2 (change p 86 none) else d0 (change p 86 none)) = d5 p
  rw [sub1033, sub1032]
  rfl
theorem sub1037 (p : Pattern) : d6 (change p 86 none) = d6 p := by
  change (if p 159 then d5 (change p 86 none) else d4 (change p 86 none)) = d6 p
  rw [sub1036, sub1035]
  rfl
theorem sub1038 (p : Pattern) : d7 (change p 86 none) = d7 p := by
  change (if p 159 then d2 (change p 86 none) else d4 (change p 86 none)) = d7 p
  rw [sub1033, sub1035]
  rfl
theorem sub1039 (p : Pattern) : d8 (change p 86 none) = d8 p := by
  change (if p 158 then d7 (change p 86 none) else d6 (change p 86 none)) = d8 p
  rw [sub1038, sub1037]
  rfl
theorem sub1040 (p : Pattern) : d1 (change p 86 none) = d1 p := by
  rfl
theorem sub1041 (p : Pattern) : d9 (change p 86 none) = d9 p := by
  change (if p 161 then d2 (change p 86 none) else d1 (change p 86 none)) = d9 p
  rw [sub1033, sub1040]
  rfl
theorem sub1042 (p : Pattern) : d10 (change p 86 none) = d10 p := by
  change (if p 160 then d9 (change p 86 none) else d1 (change p 86 none)) = d10 p
  rw [sub1041, sub1040]
  rfl
theorem sub1043 (p : Pattern) : d11 (change p 86 none) = d11 p := by
  change (if p 160 then d2 (change p 86 none) else d1 (change p 86 none)) = d11 p
  rw [sub1033, sub1040]
  rfl
theorem sub1044 (p : Pattern) : d12 (change p 86 none) = d12 p := by
  change (if p 159 then d11 (change p 86 none) else d10 (change p 86 none)) = d12 p
  rw [sub1043, sub1042]
  rfl
theorem sub1045 (p : Pattern) : d13 (change p 86 none) = d13 p := by
  change (if p 159 then d2 (change p 86 none) else d10 (change p 86 none)) = d13 p
  rw [sub1033, sub1042]
  rfl
theorem sub1046 (p : Pattern) : d14 (change p 86 none) = d14 p := by
  change (if p 158 then d13 (change p 86 none) else d12 (change p 86 none)) = d14 p
  rw [sub1045, sub1044]
  rfl
theorem sub1047 (p : Pattern) : d15 (change p 86 none) = d15 p := by
  change (if p 139 then d14 (change p 86 none) else d8 (change p 86 none)) = d15 p
  rw [sub1046, sub1039]
  rfl
theorem sub1048 (p : Pattern) : d16 (change p 86 none) = d16 p := by
  change (if p 138 then d15 (change p 86 none) else d8 (change p 86 none)) = d16 p
  rw [sub1047, sub1039]
  rfl
theorem sub1049 (p : Pattern) : d17 (change p 86 none) = d17 p := by
  change (if p 160 then d2 (change p 86 none) else d3 (change p 86 none)) = d17 p
  rw [sub1033, sub1034]
  rfl
theorem sub1050 (p : Pattern) : d18 (change p 86 none) = d18 p := by
  change (if p 159 then d17 (change p 86 none) else d4 (change p 86 none)) = d18 p
  rw [sub1049, sub1035]
  rfl
theorem sub1051 (p : Pattern) : d19 (change p 86 none) = d19 p := by
  change (if p 159 then d2 (change p 86 none) else d17 (change p 86 none)) = d19 p
  rw [sub1033, sub1049]
  rfl
theorem sub1052 (p : Pattern) : d20 (change p 86 none) = d20 p := by
  change (if p 158 then d19 (change p 86 none) else d18 (change p 86 none)) = d20 p
  rw [sub1051, sub1050]
  rfl
theorem sub1053 (p : Pattern) : d21 (change p 86 none) = d21 p := by
  change (if p 160 then d2 (change p 86 none) else d9 (change p 86 none)) = d21 p
  rw [sub1033, sub1041]
  rfl
theorem sub1054 (p : Pattern) : d22 (change p 86 none) = d22 p := by
  change (if p 159 then d21 (change p 86 none) else d10 (change p 86 none)) = d22 p
  rw [sub1053, sub1042]
  rfl
theorem sub1055 (p : Pattern) : d23 (change p 86 none) = d23 p := by
  change (if p 159 then d2 (change p 86 none) else d21 (change p 86 none)) = d23 p
  rw [sub1033, sub1053]
  rfl
theorem sub1056 (p : Pattern) : d24 (change p 86 none) = d24 p := by
  change (if p 158 then d23 (change p 86 none) else d22 (change p 86 none)) = d24 p
  rw [sub1055, sub1054]
  rfl
theorem sub1057 (p : Pattern) : d25 (change p 86 none) = d25 p := by
  change (if p 139 then d24 (change p 86 none) else d20 (change p 86 none)) = d25 p
  rw [sub1056, sub1052]
  rfl
theorem sub1058 (p : Pattern) : d26 (change p 86 none) = d26 p := by
  change (if p 138 then d25 (change p 86 none) else d20 (change p 86 none)) = d26 p
  rw [sub1057, sub1052]
  rfl
theorem sub1059 (p : Pattern) : d27 (change p 86 none) = d27 p := by
  change (if p 134 then d26 (change p 86 none) else d16 (change p 86 none)) = d27 p
  rw [sub1058, sub1048]
  rfl
theorem sub1060 (p : Pattern) : d28 (change p 86 none) = d28 p := by
  change (if p 133 then d27 (change p 86 none) else d16 (change p 86 none)) = d28 p
  rw [sub1059, sub1048]
  rfl
theorem sub1061 (p : Pattern) : d29 (change p 86 none) = d29 p := by
  change (if p 161 then d1 (change p 86 none) else d0 (change p 86 none)) = d29 p
  rw [sub1040, sub1032]
  rfl
theorem sub1062 (p : Pattern) : d30 (change p 86 none) = d30 p := by
  change (if p 160 then d2 (change p 86 none) else d29 (change p 86 none)) = d30 p
  rw [sub1033, sub1061]
  rfl
theorem sub1063 (p : Pattern) : d31 (change p 86 none) = d31 p := by
  change (if p 159 then d30 (change p 86 none) else d4 (change p 86 none)) = d31 p
  rw [sub1062, sub1035]
  rfl
theorem sub1064 (p : Pattern) : d32 (change p 86 none) = d32 p := by
  change (if p 159 then d2 (change p 86 none) else d30 (change p 86 none)) = d32 p
  rw [sub1033, sub1062]
  rfl
theorem sub1065 (p : Pattern) : d33 (change p 86 none) = d33 p := by
  change (if p 158 then d32 (change p 86 none) else d31 (change p 86 none)) = d33 p
  rw [sub1064, sub1063]
  rfl
theorem sub1066 (p : Pattern) : d34 (change p 86 none) = d34 p := by
  change (if p 139 then d24 (change p 86 none) else d33 (change p 86 none)) = d34 p
  rw [sub1056, sub1065]
  rfl
theorem sub1067 (p : Pattern) : d35 (change p 86 none) = d35 p := by
  change (if p 138 then d34 (change p 86 none) else d33 (change p 86 none)) = d35 p
  rw [sub1066, sub1065]
  rfl
theorem sub1068 (p : Pattern) : d36 (change p 86 none) = d36 p := by
  change (if p 134 then d35 (change p 86 none) else d16 (change p 86 none)) = d36 p
  rw [sub1067, sub1048]
  rfl
theorem sub1069 (p : Pattern) : d37 (change p 86 none) = d37 p := by
  change (if p 159 then d2 (change p 86 none) else d5 (change p 86 none)) = d37 p
  rw [sub1033, sub1036]
  rfl
theorem sub1070 (p : Pattern) : d38 (change p 86 none) = d38 p := by
  change (if p 158 then d37 (change p 86 none) else d6 (change p 86 none)) = d38 p
  rw [sub1069, sub1037]
  rfl
theorem sub1071 (p : Pattern) : d39 (change p 86 none) = d39 p := by
  change (if p 159 then d2 (change p 86 none) else d11 (change p 86 none)) = d39 p
  rw [sub1033, sub1043]
  rfl
theorem sub1072 (p : Pattern) : d40 (change p 86 none) = d40 p := by
  change (if p 158 then d39 (change p 86 none) else d12 (change p 86 none)) = d40 p
  rw [sub1071, sub1044]
  rfl
theorem sub1073 (p : Pattern) : d41 (change p 86 none) = d41 p := by
  change (if p 139 then d40 (change p 86 none) else d38 (change p 86 none)) = d41 p
  rw [sub1072, sub1070]
  rfl
theorem sub1074 (p : Pattern) : d42 (change p 86 none) = d42 p := by
  change (if p 138 then d41 (change p 86 none) else d38 (change p 86 none)) = d42 p
  rw [sub1073, sub1070]
  rfl
theorem sub1075 (p : Pattern) : d43 (change p 86 none) = d43 p := by
  change (if p 134 then d26 (change p 86 none) else d42 (change p 86 none)) = d43 p
  rw [sub1058, sub1074]
  rfl
theorem sub1076 (p : Pattern) : d44 (change p 86 none) = d44 p := by
  change (if p 133 then d43 (change p 86 none) else d36 (change p 86 none)) = d44 p
  rw [sub1075, sub1068]
  rfl
theorem sub1077 (p : Pattern) : d45 (change p 86 none) = d45 p := by
  change (if p 132 then d44 (change p 86 none) else d28 (change p 86 none)) = d45 p
  rw [sub1076, sub1060]
  rfl
theorem sub1078 (p : Pattern) : d46 (change p 86 none) = d46 p := by
  change (if p 134 then d25 (change p 86 none) else d15 (change p 86 none)) = d46 p
  rw [sub1057, sub1047]
  rfl
theorem sub1079 (p : Pattern) : d47 (change p 86 none) = d47 p := by
  change (if p 133 then d46 (change p 86 none) else d15 (change p 86 none)) = d47 p
  rw [sub1078, sub1047]
  rfl
end NetHack.Sokoban32Refined
