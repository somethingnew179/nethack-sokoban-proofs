/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub960 (p : Pattern) : d36 (change p 71 none) = d36 p := by
  change (if p 204 then d12 (change p 71 none) else d35 (change p 71 none)) = d36 p
  rw [sub932, sub959]
  rfl
theorem sub961 (p : Pattern) : d37 (change p 71 none) = d37 p := by
  change (if p 182 then d36 (change p 71 none) else d14 (change p 71 none)) = d37 p
  rw [sub960, sub934]
  rfl
theorem sub962 (p : Pattern) : d38 (change p 71 none) = d38 p := by
  change (if p 163 then d37 (change p 71 none) else d33 (change p 71 none)) = d38 p
  rw [sub961, sub956]
  rfl
theorem sub963 (p : Pattern) : d11 (change p 71 none) = d11 p := by
  rfl
theorem sub964 (p : Pattern) : d39 (change p 71 none) = d39 p := by
  change (if p 247 then d12 (change p 71 none) else d11 (change p 71 none)) = d39 p
  rw [sub932, sub963]
  rfl
theorem sub965 (p : Pattern) : d40 (change p 71 none) = d40 p := by
  change (if p 246 then d39 (change p 71 none) else d11 (change p 71 none)) = d40 p
  rw [sub964, sub963]
  rfl
theorem sub966 (p : Pattern) : d41 (change p 71 none) = d41 p := by
  change (if p 204 then d12 (change p 71 none) else d40 (change p 71 none)) = d41 p
  rw [sub932, sub965]
  rfl
theorem sub967 (p : Pattern) : d42 (change p 71 none) = d42 p := by
  change (if p 182 then d41 (change p 71 none) else d14 (change p 71 none)) = d42 p
  rw [sub966, sub934]
  rfl
theorem sub968 (p : Pattern) : d43 (change p 71 none) = d43 p := by
  change (if p 182 then d12 (change p 71 none) else d18 (change p 71 none)) = d43 p
  rw [sub932, sub939]
  rfl
theorem sub969 (p : Pattern) : d44 (change p 71 none) = d44 p := by
  change (if p 163 then d43 (change p 71 none) else d42 (change p 71 none)) = d44 p
  rw [sub968, sub967]
  rfl
theorem sub970 (p : Pattern) : d45 (change p 71 none) = d45 p := by
  change (if p 162 then d44 (change p 71 none) else d38 (change p 71 none)) = d45 p
  rw [sub969, sub962]
  rfl
theorem sub971 (p : Pattern) : d46 (change p 71 none) = d46 p := by
  change (if p 182 then d12 (change p 71 none) else d14 (change p 71 none)) = d46 p
  rw [sub932, sub934]
  rfl
theorem sub972 (p : Pattern) : d47 (change p 71 none) = d47 p := by
  change (if p 163 then d43 (change p 71 none) else d46 (change p 71 none)) = d47 p
  rw [sub968, sub971]
  rfl
theorem sub973 (p : Pattern) : d48 (change p 71 none) = d48 p := by
  change (if p 182 then d12 (change p 71 none) else d24 (change p 71 none)) = d48 p
  rw [sub932, sub946]
  rfl
theorem sub974 (p : Pattern) : d49 (change p 71 none) = d49 p := by
  change (if p 163 then d12 (change p 71 none) else d48 (change p 71 none)) = d49 p
  rw [sub932, sub973]
  rfl
theorem sub975 (p : Pattern) : d50 (change p 71 none) = d50 p := by
  change (if p 162 then d49 (change p 71 none) else d47 (change p 71 none)) = d50 p
  rw [sub974, sub972]
  rfl
theorem sub976 (p : Pattern) : d51 (change p 71 none) = d51 p := by
  change (if p 161 then d50 (change p 71 none) else d45 (change p 71 none)) = d51 p
  rw [sub975, sub970]
  rfl
theorem sub977 (p : Pattern) : d52 (change p 71 none) = d52 p := by
  change (if p 160 then d51 (change p 71 none) else d29 (change p 71 none)) = d52 p
  rw [sub976, sub951]
  rfl
theorem sub978 (p : Pattern) : d53 (change p 71 none) = d53 p := by
  change (if p 182 then d32 (change p 71 none) else d31 (change p 71 none)) = d53 p
  rw [sub955, sub954]
  rfl
theorem sub979 (p : Pattern) : d54 (change p 71 none) = d54 p := by
  change (if p 163 then d53 (change p 71 none) else d16 (change p 71 none)) = d54 p
  rw [sub978, sub936]
  rfl
theorem sub980 (p : Pattern) : d55 (change p 71 none) = d55 p := by
  change (if p 163 then d26 (change p 71 none) else d20 (change p 71 none)) = d55 p
  rw [sub948, sub941]
  rfl
theorem sub981 (p : Pattern) : d56 (change p 71 none) = d56 p := by
  change (if p 162 then d55 (change p 71 none) else d54 (change p 71 none)) = d56 p
  rw [sub980, sub979]
  rfl
theorem sub982 (p : Pattern) : d10 (change p 71 none) = d10 p := by
  rfl
theorem sub983 (p : Pattern) : d57 (change p 71 none) = d57 p := by
  change (if p 247 then d12 (change p 71 none) else d10 (change p 71 none)) = d57 p
  rw [sub932, sub982]
  rfl
theorem sub984 (p : Pattern) : d58 (change p 71 none) = d58 p := by
  change (if p 246 then d57 (change p 71 none) else d10 (change p 71 none)) = d58 p
  rw [sub983, sub982]
  rfl
theorem sub985 (p : Pattern) : d59 (change p 71 none) = d59 p := by
  change (if p 204 then d12 (change p 71 none) else d58 (change p 71 none)) = d59 p
  rw [sub932, sub984]
  rfl
theorem sub986 (p : Pattern) : d60 (change p 71 none) = d60 p := by
  change (if p 182 then d59 (change p 71 none) else d58 (change p 71 none)) = d60 p
  rw [sub985, sub984]
  rfl
theorem sub987 (p : Pattern) : d61 (change p 71 none) = d61 p := by
  change (if p 163 then d60 (change p 71 none) else d20 (change p 71 none)) = d61 p
  rw [sub986, sub941]
  rfl
theorem sub988 (p : Pattern) : d62 (change p 71 none) = d62 p := by
  change (if p 182 then d41 (change p 71 none) else d40 (change p 71 none)) = d62 p
  rw [sub966, sub965]
  rfl
theorem sub989 (p : Pattern) : d63 (change p 71 none) = d63 p := by
  change (if p 163 then d12 (change p 71 none) else d62 (change p 71 none)) = d63 p
  rw [sub932, sub988]
  rfl
theorem sub990 (p : Pattern) : d64 (change p 71 none) = d64 p := by
  change (if p 162 then d63 (change p 71 none) else d61 (change p 71 none)) = d64 p
  rw [sub989, sub987]
  rfl
theorem sub991 (p : Pattern) : d65 (change p 71 none) = d65 p := by
  change (if p 161 then d64 (change p 71 none) else d56 (change p 71 none)) = d65 p
  rw [sub990, sub981]
  rfl
theorem sub992 (p : Pattern) : d66 (change p 71 none) = d66 p := by
  change (if p 182 then d12 (change p 71 none) else d31 (change p 71 none)) = d66 p
  rw [sub932, sub954]
  rfl
theorem sub993 (p : Pattern) : d67 (change p 71 none) = d67 p := by
  change (if p 163 then d66 (change p 71 none) else d37 (change p 71 none)) = d67 p
  rw [sub992, sub961]
  rfl
theorem sub994 (p : Pattern) : d68 (change p 71 none) = d68 p := by
  change (if p 163 then d48 (change p 71 none) else d43 (change p 71 none)) = d68 p
  rw [sub973, sub968]
  rfl
theorem sub995 (p : Pattern) : d69 (change p 71 none) = d69 p := by
  change (if p 162 then d68 (change p 71 none) else d67 (change p 71 none)) = d69 p
  rw [sub994, sub993]
  rfl
theorem sub996 (p : Pattern) : d70 (change p 71 none) = d70 p := by
  change (if p 182 then d12 (change p 71 none) else d58 (change p 71 none)) = d70 p
  rw [sub932, sub984]
  rfl
theorem sub997 (p : Pattern) : d71 (change p 71 none) = d71 p := by
  change (if p 163 then d70 (change p 71 none) else d43 (change p 71 none)) = d71 p
  rw [sub996, sub968]
  rfl
theorem sub998 (p : Pattern) : d72 (change p 71 none) = d72 p := by
  change (if p 182 then d12 (change p 71 none) else d40 (change p 71 none)) = d72 p
  rw [sub932, sub965]
  rfl
theorem sub999 (p : Pattern) : d73 (change p 71 none) = d73 p := by
  change (if p 163 then d12 (change p 71 none) else d72 (change p 71 none)) = d73 p
  rw [sub932, sub998]
  rfl
theorem sub1000 (p : Pattern) : d74 (change p 71 none) = d74 p := by
  change (if p 162 then d73 (change p 71 none) else d71 (change p 71 none)) = d74 p
  rw [sub999, sub997]
  rfl
theorem sub1001 (p : Pattern) : d75 (change p 71 none) = d75 p := by
  change (if p 161 then d74 (change p 71 none) else d69 (change p 71 none)) = d75 p
  rw [sub1000, sub995]
  rfl
theorem sub1002 (p : Pattern) : d76 (change p 71 none) = d76 p := by
  change (if p 160 then d75 (change p 71 none) else d65 (change p 71 none)) = d76 p
  rw [sub1001, sub991]
  rfl
theorem sub1003 (p : Pattern) : d77 (change p 71 none) = d77 p := by
  change (if p 141 then d76 (change p 71 none) else d52 (change p 71 none)) = d77 p
  rw [sub1002, sub977]
  rfl
theorem sub1004 (p : Pattern) : d78 (change p 71 none) = d78 p := by
  change (if p 182 then d36 (change p 71 none) else d35 (change p 71 none)) = d78 p
  rw [sub960, sub959]
  rfl
theorem sub1005 (p : Pattern) : d79 (change p 71 none) = d79 p := by
  change (if p 163 then d78 (change p 71 none) else d53 (change p 71 none)) = d79 p
  rw [sub1004, sub978]
  rfl
theorem sub1006 (p : Pattern) : d80 (change p 71 none) = d80 p := by
  change (if p 162 then d63 (change p 71 none) else d79 (change p 71 none)) = d80 p
  rw [sub989, sub1005]
  rfl
theorem sub1007 (p : Pattern) : d81 (change p 71 none) = d81 p := by
  change (if p 161 then d12 (change p 71 none) else d80 (change p 71 none)) = d81 p
  rw [sub932, sub1006]
  rfl
theorem sub1008 (p : Pattern) : d82 (change p 71 none) = d82 p := by
  change (if p 160 then d81 (change p 71 none) else d29 (change p 71 none)) = d82 p
  rw [sub1007, sub951]
  rfl
theorem sub1009 (p : Pattern) : d83 (change p 71 none) = d83 p := by
  change (if p 163 then d12 (change p 71 none) else d78 (change p 71 none)) = d83 p
  rw [sub932, sub1004]
  rfl
theorem sub1010 (p : Pattern) : d84 (change p 71 none) = d84 p := by
  change (if p 162 then d12 (change p 71 none) else d83 (change p 71 none)) = d84 p
  rw [sub932, sub1009]
  rfl
theorem sub1011 (p : Pattern) : d85 (change p 71 none) = d85 p := by
  change (if p 161 then d12 (change p 71 none) else d84 (change p 71 none)) = d85 p
  rw [sub932, sub1010]
  rfl
theorem sub1012 (p : Pattern) : d86 (change p 71 none) = d86 p := by
  change (if p 160 then d85 (change p 71 none) else d65 (change p 71 none)) = d86 p
  rw [sub1011, sub991]
  rfl
theorem sub1013 (p : Pattern) : d87 (change p 71 none) = d87 p := by
  change (if p 141 then d86 (change p 71 none) else d82 (change p 71 none)) = d87 p
  rw [sub1012, sub1008]
  rfl
theorem sub1014 (p : Pattern) : d88 (change p 71 none) = d88 p := by
  change (if p 138 then d87 (change p 71 none) else d77 (change p 71 none)) = d88 p
  rw [sub1013, sub1003]
  rfl
theorem sub1015 (p : Pattern) : d89 (change p 71 none) = d89 p := by
  change (if p 163 then d62 (change p 71 none) else d26 (change p 71 none)) = d89 p
  rw [sub988, sub948]
  rfl
theorem sub1016 (p : Pattern) : d90 (change p 71 none) = d90 p := by
  change (if p 162 then d63 (change p 71 none) else d89 (change p 71 none)) = d90 p
  rw [sub989, sub1015]
  rfl
theorem sub1017 (p : Pattern) : d91 (change p 71 none) = d91 p := by
  change (if p 162 then d12 (change p 71 none) else d63 (change p 71 none)) = d91 p
  rw [sub932, sub989]
  rfl
theorem sub1018 (p : Pattern) : d92 (change p 71 none) = d92 p := by
  change (if p 161 then d91 (change p 71 none) else d90 (change p 71 none)) = d92 p
  rw [sub1017, sub1016]
  rfl
theorem sub1019 (p : Pattern) : d93 (change p 71 none) = d93 p := by
  change (if p 161 then d12 (change p 71 none) else d91 (change p 71 none)) = d93 p
  rw [sub932, sub1017]
  rfl
theorem sub1020 (p : Pattern) : d94 (change p 71 none) = d94 p := by
  change (if p 160 then d93 (change p 71 none) else d92 (change p 71 none)) = d94 p
  rw [sub1019, sub1018]
  rfl
theorem sub1021 (p : Pattern) : d95 (change p 71 none) = d95 p := by
  change (if p 160 then d12 (change p 71 none) else d93 (change p 71 none)) = d95 p
  rw [sub932, sub1019]
  rfl
theorem sub1022 (p : Pattern) : d96 (change p 71 none) = d96 p := by
  change (if p 141 then d95 (change p 71 none) else d94 (change p 71 none)) = d96 p
  rw [sub1021, sub1020]
  rfl
theorem sub1023 (p : Pattern) : d97 (change p 71 none) = d97 p := by
  change (if p 138 then d96 (change p 71 none) else d87 (change p 71 none)) = d97 p
  rw [sub1022, sub1013]
  rfl
theorem sub1024 (p : Pattern) : d98 (change p 71 none) = d98 p := by
  change (if p 116 then d97 (change p 71 none) else d88 (change p 71 none)) = d98 p
  rw [sub1023, sub1014]
  rfl
theorem sub1025 (p : Pattern) : d99 (change p 71 none) = d99 p := by
  change (if p 138 then d12 (change p 71 none) else d87 (change p 71 none)) = d99 p
  rw [sub932, sub1013]
  rfl
theorem sub1026 (p : Pattern) : d100 (change p 71 none) = d100 p := by
  change (if p 116 then d99 (change p 71 none) else d88 (change p 71 none)) = d100 p
  rw [sub1025, sub1014]
  rfl
theorem sub1027 (p : Pattern) : d101 (change p 71 none) = d101 p := by
  change (if p 115 then d100 (change p 71 none) else d98 (change p 71 none)) = d101 p
  rw [sub1026, sub1024]
  rfl
theorem sub1028 (p : Pattern) : d485 (change p 71 none) = d101 p := by
  change d101 (change p 71 none) = d101 p
  exact sub1027 p
theorem sub1029 (p : Pattern) : d486 (change p 71 none) = d101 p := by
  change d101 (change p 71 none) = d101 p
  exact sub1027 p
theorem sub1030 (p : Pattern) : d487 (change p 71 none) = d101 p := by
  change (if p 49 then d486 (change p 71 none) else d485 (change p 71 none)) = d101 p
  rw [sub1029, sub1028]
  simp only [ite_self]
theorem sub1031 (p : Pattern) : d488 (change p 71 none) = d101 p := by
  change (if p 48 then d487 (change p 71 none) else d485 (change p 71 none)) = d101 p
  rw [sub1030, sub1028]
  simp only [ite_self]
theorem sub1032 (p : Pattern) : d0 (change p 48 none) = d0 p := by
  rfl
theorem sub1033 (p : Pattern) : d12 (change p 48 none) = d12 p := by
  rfl
theorem sub1034 (p : Pattern) : d13 (change p 48 none) = d13 p := by
  change (if p 247 then d12 (change p 48 none) else d0 (change p 48 none)) = d13 p
  rw [sub1033, sub1032]
  rfl
theorem sub1035 (p : Pattern) : d14 (change p 48 none) = d14 p := by
  change (if p 246 then d13 (change p 48 none) else d0 (change p 48 none)) = d14 p
  rw [sub1034, sub1032]
  rfl
theorem sub1036 (p : Pattern) : d15 (change p 48 none) = d15 p := by
  change (if p 204 then d12 (change p 48 none) else d14 (change p 48 none)) = d15 p
  rw [sub1033, sub1035]
  rfl
theorem sub1037 (p : Pattern) : d16 (change p 48 none) = d16 p := by
  change (if p 182 then d15 (change p 48 none) else d14 (change p 48 none)) = d16 p
  rw [sub1036, sub1035]
  rfl
theorem sub1038 (p : Pattern) : d4 (change p 48 none) = d4 p := by
  rfl
theorem sub1039 (p : Pattern) : d17 (change p 48 none) = d17 p := by
  change (if p 247 then d12 (change p 48 none) else d4 (change p 48 none)) = d17 p
  rw [sub1033, sub1038]
  rfl
theorem sub1040 (p : Pattern) : d18 (change p 48 none) = d18 p := by
  change (if p 246 then d17 (change p 48 none) else d4 (change p 48 none)) = d18 p
  rw [sub1039, sub1038]
  rfl
theorem sub1041 (p : Pattern) : d19 (change p 48 none) = d19 p := by
  change (if p 204 then d12 (change p 48 none) else d18 (change p 48 none)) = d19 p
  rw [sub1033, sub1040]
  rfl
theorem sub1042 (p : Pattern) : d20 (change p 48 none) = d20 p := by
  change (if p 182 then d19 (change p 48 none) else d18 (change p 48 none)) = d20 p
  rw [sub1041, sub1040]
  rfl
theorem sub1043 (p : Pattern) : d21 (change p 48 none) = d21 p := by
  change (if p 163 then d20 (change p 48 none) else d16 (change p 48 none)) = d21 p
  rw [sub1042, sub1037]
  rfl
theorem sub1044 (p : Pattern) : d22 (change p 48 none) = d22 p := by
  change (if p 162 then d21 (change p 48 none) else d16 (change p 48 none)) = d22 p
  rw [sub1043, sub1037]
  rfl
theorem sub1045 (p : Pattern) : d9 (change p 48 none) = d9 p := by
  rfl
theorem sub1046 (p : Pattern) : d23 (change p 48 none) = d23 p := by
  change (if p 247 then d12 (change p 48 none) else d9 (change p 48 none)) = d23 p
  rw [sub1033, sub1045]
  rfl
theorem sub1047 (p : Pattern) : d24 (change p 48 none) = d24 p := by
  change (if p 246 then d23 (change p 48 none) else d9 (change p 48 none)) = d24 p
  rw [sub1046, sub1045]
  rfl
theorem sub1048 (p : Pattern) : d25 (change p 48 none) = d25 p := by
  change (if p 204 then d12 (change p 48 none) else d24 (change p 48 none)) = d25 p
  rw [sub1033, sub1047]
  rfl
theorem sub1049 (p : Pattern) : d26 (change p 48 none) = d26 p := by
  change (if p 182 then d25 (change p 48 none) else d24 (change p 48 none)) = d26 p
  rw [sub1048, sub1047]
  rfl
theorem sub1050 (p : Pattern) : d27 (change p 48 none) = d27 p := by
  change (if p 163 then d12 (change p 48 none) else d26 (change p 48 none)) = d27 p
  rw [sub1033, sub1049]
  rfl
theorem sub1051 (p : Pattern) : d28 (change p 48 none) = d28 p := by
  change (if p 162 then d27 (change p 48 none) else d21 (change p 48 none)) = d28 p
  rw [sub1050, sub1043]
  rfl
theorem sub1052 (p : Pattern) : d29 (change p 48 none) = d29 p := by
  change (if p 161 then d28 (change p 48 none) else d22 (change p 48 none)) = d29 p
  rw [sub1051, sub1044]
  rfl
theorem sub1053 (p : Pattern) : d2 (change p 48 none) = d2 p := by
  rfl
theorem sub1054 (p : Pattern) : d30 (change p 48 none) = d30 p := by
  change (if p 247 then d12 (change p 48 none) else d2 (change p 48 none)) = d30 p
  rw [sub1033, sub1053]
  rfl
theorem sub1055 (p : Pattern) : d31 (change p 48 none) = d31 p := by
  change (if p 246 then d30 (change p 48 none) else d2 (change p 48 none)) = d31 p
  rw [sub1054, sub1053]
  rfl
theorem sub1056 (p : Pattern) : d32 (change p 48 none) = d32 p := by
  change (if p 204 then d12 (change p 48 none) else d31 (change p 48 none)) = d32 p
  rw [sub1033, sub1055]
  rfl
theorem sub1057 (p : Pattern) : d33 (change p 48 none) = d33 p := by
  change (if p 182 then d32 (change p 48 none) else d14 (change p 48 none)) = d33 p
  rw [sub1056, sub1035]
  rfl
theorem sub1058 (p : Pattern) : d6 (change p 48 none) = d6 p := by
  rfl
theorem sub1059 (p : Pattern) : d34 (change p 48 none) = d34 p := by
  change (if p 247 then d12 (change p 48 none) else d6 (change p 48 none)) = d34 p
  rw [sub1033, sub1058]
  rfl
theorem sub1060 (p : Pattern) : d35 (change p 48 none) = d35 p := by
  change (if p 246 then d34 (change p 48 none) else d6 (change p 48 none)) = d35 p
  rw [sub1059, sub1058]
  rfl
theorem sub1061 (p : Pattern) : d36 (change p 48 none) = d36 p := by
  change (if p 204 then d12 (change p 48 none) else d35 (change p 48 none)) = d36 p
  rw [sub1033, sub1060]
  rfl
theorem sub1062 (p : Pattern) : d37 (change p 48 none) = d37 p := by
  change (if p 182 then d36 (change p 48 none) else d14 (change p 48 none)) = d37 p
  rw [sub1061, sub1035]
  rfl
theorem sub1063 (p : Pattern) : d38 (change p 48 none) = d38 p := by
  change (if p 163 then d37 (change p 48 none) else d33 (change p 48 none)) = d38 p
  rw [sub1062, sub1057]
  rfl
theorem sub1064 (p : Pattern) : d11 (change p 48 none) = d11 p := by
  rfl
theorem sub1065 (p : Pattern) : d39 (change p 48 none) = d39 p := by
  change (if p 247 then d12 (change p 48 none) else d11 (change p 48 none)) = d39 p
  rw [sub1033, sub1064]
  rfl
theorem sub1066 (p : Pattern) : d40 (change p 48 none) = d40 p := by
  change (if p 246 then d39 (change p 48 none) else d11 (change p 48 none)) = d40 p
  rw [sub1065, sub1064]
  rfl
theorem sub1067 (p : Pattern) : d41 (change p 48 none) = d41 p := by
  change (if p 204 then d12 (change p 48 none) else d40 (change p 48 none)) = d41 p
  rw [sub1033, sub1066]
  rfl
theorem sub1068 (p : Pattern) : d42 (change p 48 none) = d42 p := by
  change (if p 182 then d41 (change p 48 none) else d14 (change p 48 none)) = d42 p
  rw [sub1067, sub1035]
  rfl
theorem sub1069 (p : Pattern) : d43 (change p 48 none) = d43 p := by
  change (if p 182 then d12 (change p 48 none) else d18 (change p 48 none)) = d43 p
  rw [sub1033, sub1040]
  rfl
theorem sub1070 (p : Pattern) : d44 (change p 48 none) = d44 p := by
  change (if p 163 then d43 (change p 48 none) else d42 (change p 48 none)) = d44 p
  rw [sub1069, sub1068]
  rfl
theorem sub1071 (p : Pattern) : d45 (change p 48 none) = d45 p := by
  change (if p 162 then d44 (change p 48 none) else d38 (change p 48 none)) = d45 p
  rw [sub1070, sub1063]
  rfl
theorem sub1072 (p : Pattern) : d46 (change p 48 none) = d46 p := by
  change (if p 182 then d12 (change p 48 none) else d14 (change p 48 none)) = d46 p
  rw [sub1033, sub1035]
  rfl
theorem sub1073 (p : Pattern) : d47 (change p 48 none) = d47 p := by
  change (if p 163 then d43 (change p 48 none) else d46 (change p 48 none)) = d47 p
  rw [sub1069, sub1072]
  rfl
theorem sub1074 (p : Pattern) : d48 (change p 48 none) = d48 p := by
  change (if p 182 then d12 (change p 48 none) else d24 (change p 48 none)) = d48 p
  rw [sub1033, sub1047]
  rfl
theorem sub1075 (p : Pattern) : d49 (change p 48 none) = d49 p := by
  change (if p 163 then d12 (change p 48 none) else d48 (change p 48 none)) = d49 p
  rw [sub1033, sub1074]
  rfl
theorem sub1076 (p : Pattern) : d50 (change p 48 none) = d50 p := by
  change (if p 162 then d49 (change p 48 none) else d47 (change p 48 none)) = d50 p
  rw [sub1075, sub1073]
  rfl
theorem sub1077 (p : Pattern) : d51 (change p 48 none) = d51 p := by
  change (if p 161 then d50 (change p 48 none) else d45 (change p 48 none)) = d51 p
  rw [sub1076, sub1071]
  rfl
theorem sub1078 (p : Pattern) : d52 (change p 48 none) = d52 p := by
  change (if p 160 then d51 (change p 48 none) else d29 (change p 48 none)) = d52 p
  rw [sub1077, sub1052]
  rfl
theorem sub1079 (p : Pattern) : d53 (change p 48 none) = d53 p := by
  change (if p 182 then d32 (change p 48 none) else d31 (change p 48 none)) = d53 p
  rw [sub1056, sub1055]
  rfl
end NetHack.Sokoban22Refined85
