/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions46
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s7050 (pattern : Twelve) : d45 (change pattern 0 12) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d1 (change pattern 0 12)) = d45 pattern
  rw [s6978, s6962]
  rfl
theorem s7051 (pattern : Twelve) : d65 (change pattern 0 12) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 0 12) else d30 (change pattern 0 12)) = d65 pattern
  rw [s7050, s6983]
  rfl
theorem s7052 (pattern : Twelve) : d85 (change pattern 0 12) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 0 12) else d56 (change pattern 0 12)) = d85 pattern
  rw [s7051, s7008]
  rfl
theorem s7053 (pattern : Twelve) : d66 (change pattern 0 12) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 0 12) else d30 (change pattern 0 12)) = d66 pattern
  rw [s7022, s6983]
  rfl
theorem s7054 (pattern : Twelve) : d86 (change pattern 0 12) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 0 12) else d66 (change pattern 0 12)) = d86 pattern
  rw [s7046, s7053]
  rfl
theorem s7055 (pattern : Twelve) : d99 (change pattern 0 12) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 0 12) else d85 (change pattern 0 12)) = d99 pattern
  rw [s7054, s7052]
  rfl
theorem s7056 (pattern : Twelve) : d107 (change pattern 0 12) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 0 12) else d97 (change pattern 0 12)) = d107 pattern
  rw [s7055, s7040]
  rfl
theorem s7057 (pattern : Twelve) : d112 (change pattern 0 12) = d112 pattern := by
  change (if pattern.d then d107 (change pattern 0 12) else d106 (change pattern 0 12)) = d112 pattern
  rw [s7056, s7049]
  rfl
theorem s7058 (pattern : Twelve) : d46 (change pattern 0 12) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 0 12) else d1 (change pattern 0 12)) = d46 pattern
  rw [s6971, s6962]
  rfl
theorem s7059 (pattern : Twelve) : d67 (change pattern 0 12) = d67 pattern := by
  change (if pattern.h then d46 (change pattern 0 12) else d30 (change pattern 0 12)) = d67 pattern
  rw [s7058, s6983]
  rfl
theorem s7060 (pattern : Twelve) : d87 (change pattern 0 12) = d87 pattern := by
  change (if pattern.f then d67 (change pattern 0 12) else d30 (change pattern 0 12)) = d87 pattern
  rw [s7059, s6983]
  rfl
theorem s7061 (pattern : Twelve) : d68 (change pattern 0 12) = d68 pattern := by
  change (if pattern.h then d38 (change pattern 0 12) else d30 (change pattern 0 12)) = d68 pattern
  rw [s7021, s6983]
  rfl
theorem s7062 (pattern : Twelve) : d88 (change pattern 0 12) = d88 pattern := by
  change (if pattern.f then d64 (change pattern 0 12) else d68 (change pattern 0 12)) = d88 pattern
  rw [s7046, s7061]
  rfl
theorem s7063 (pattern : Twelve) : d100 (change pattern 0 12) = d100 pattern := by
  change (if pattern.e then d88 (change pattern 0 12) else d87 (change pattern 0 12)) = d100 pattern
  rw [s7062, s7060]
  rfl
theorem s7064 (pattern : Twelve) : d47 (change pattern 0 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d3 (change pattern 0 12)) = d47 pattern
  rw [s6978, s6971]
  rfl
theorem s7065 (pattern : Twelve) : d69 (change pattern 0 12) = d69 pattern := by
  change (if pattern.h then d47 (change pattern 0 12) else d38 (change pattern 0 12)) = d69 pattern
  rw [s7064, s7021]
  rfl
theorem s7066 (pattern : Twelve) : d89 (change pattern 0 12) = d89 pattern := by
  change (if pattern.f then d69 (change pattern 0 12) else d59 (change pattern 0 12)) = d89 pattern
  rw [s7065, s7023]
  rfl
theorem s7067 (pattern : Twelve) : d48 (change pattern 0 12) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d4 (change pattern 0 12)) = d48 pattern
  rw [s6978, s6986]
  rfl
theorem s7068 (pattern : Twelve) : d70 (change pattern 0 12) = d70 pattern := by
  change (if pattern.h then d48 (change pattern 0 12) else d38 (change pattern 0 12)) = d70 pattern
  rw [s7067, s7021]
  rfl
theorem s7069 (pattern : Twelve) : d49 (change pattern 0 12) = d49 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d24 (change pattern 0 12)) = d49 pattern
  rw [s6978, s7028]
  rfl
theorem s7070 (pattern : Twelve) : d71 (change pattern 0 12) = d71 pattern := by
  change (if pattern.h then d49 (change pattern 0 12) else d41 (change pattern 0 12)) = d71 pattern
  rw [s7069, s7029]
  rfl
theorem s7071 (pattern : Twelve) : d90 (change pattern 0 12) = d90 pattern := by
  change (if pattern.f then d71 (change pattern 0 12) else d70 (change pattern 0 12)) = d90 pattern
  rw [s7070, s7068]
  rfl
theorem s7072 (pattern : Twelve) : d101 (change pattern 0 12) = d101 pattern := by
  change (if pattern.e then d90 (change pattern 0 12) else d89 (change pattern 0 12)) = d101 pattern
  rw [s7071, s7066]
  rfl
theorem s7073 (pattern : Twelve) : d108 (change pattern 0 12) = d108 pattern := by
  change (if pattern.j then d101 (change pattern 0 12) else d100 (change pattern 0 12)) = d108 pattern
  rw [s7072, s7063]
  rfl
theorem s7074 (pattern : Twelve) : d109 (change pattern 0 12) = d109 pattern := by
  change (if pattern.j then d6 (change pattern 0 12) else d99 (change pattern 0 12)) = d109 pattern
  rw [s6978, s7055]
  rfl
theorem s7075 (pattern : Twelve) : d113 (change pattern 0 12) = d113 pattern := by
  change (if pattern.d then d109 (change pattern 0 12) else d108 (change pattern 0 12)) = d113 pattern
  rw [s7074, s7073]
  rfl
theorem s7076 (pattern : Twelve) : d115 (change pattern 0 12) = d115 pattern := by
  change (if pattern.c then d113 (change pattern 0 12) else d112 (change pattern 0 12)) = d115 pattern
  rw [s7075, s7057]
  rfl
theorem s7077 (pattern : Twelve) : d116 (change pattern 0 12) = d116 pattern := by
  change (if pattern.g then d115 (change pattern 0 12) else d114 (change pattern 0 12)) = d116 pattern
  rw [s7076, s7039]
  rfl
theorem s7078 (pattern : Twelve) : d813 (change pattern 0 12) = d116 pattern := by
  change d116 (change pattern 0 12) = d116 pattern
  exact s7077 pattern
theorem s7079 (pattern : Twelve) : d814 (change pattern 0 12) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 0 12) else d7 (change pattern 0 12)) = d814 pattern
  rw [s6962, s6964]
  rfl
theorem s7080 (pattern : Twelve) : d816 (change pattern 0 12) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 0 12) else d814 (change pattern 0 12)) = d816 pattern
  rw [s6962, s7079]
  rfl
theorem s7081 (pattern : Twelve) : d824 (change pattern 0 12) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 0 12) else d27 (change pattern 0 12)) = d824 pattern
  rw [s7080, s6966]
  rfl
theorem s7082 (pattern : Twelve) : d838 (change pattern 0 12) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 0 12) else d0 (change pattern 0 12)) = d838 pattern
  rw [s7081, s6961]
  rfl
theorem s7083 (pattern : Twelve) : d817 (change pattern 0 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 0 12) else d19 (change pattern 0 12)) = d817 pattern
  rw [s7031, s6977]
  rfl
theorem s7084 (pattern : Twelve) : d825 (change pattern 0 12) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 0 12) else d817 (change pattern 0 12)) = d825 pattern
  rw [s7032, s7083]
  rfl
theorem s7085 (pattern : Twelve) : d839 (change pattern 0 12) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 0 12) else d17 (change pattern 0 12)) = d839 pattern
  rw [s7084, s6965]
  rfl
theorem s7086 (pattern : Twelve) : d853 (change pattern 0 12) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 0 12) else d838 (change pattern 0 12)) = d853 pattern
  rw [s7085, s7082]
  rfl
theorem s7087 (pattern : Twelve) : d818 (change pattern 0 12) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d814 (change pattern 0 12)) = d818 pattern
  rw [s6978, s7079]
  rfl
theorem s7088 (pattern : Twelve) : d826 (change pattern 0 12) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 0 12) else d34 (change pattern 0 12)) = d826 pattern
  rw [s7087, s7000]
  rfl
theorem s7089 (pattern : Twelve) : d840 (change pattern 0 12) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 0 12) else d56 (change pattern 0 12)) = d840 pattern
  rw [s7088, s7008]
  rfl
theorem s7090 (pattern : Twelve) : d827 (change pattern 0 12) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 0 12) else d34 (change pattern 0 12)) = d827 pattern
  rw [s7009, s7000]
  rfl
theorem s7091 (pattern : Twelve) : d841 (change pattern 0 12) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 0 12) else d827 (change pattern 0 12)) = d841 pattern
  rw [s7084, s7090]
  rfl
theorem s7092 (pattern : Twelve) : d854 (change pattern 0 12) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 0 12) else d840 (change pattern 0 12)) = d854 pattern
  rw [s7091, s7089]
  rfl
theorem s7093 (pattern : Twelve) : d861 (change pattern 0 12) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 0 12) else d853 (change pattern 0 12)) = d861 pattern
  rw [s7092, s7086]
  rfl
theorem s7094 (pattern : Twelve) : d819 (change pattern 0 12) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 0 12) else d814 (change pattern 0 12)) = d819 pattern
  rw [s6971, s7079]
  rfl
theorem s7095 (pattern : Twelve) : d828 (change pattern 0 12) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 0 12) else d34 (change pattern 0 12)) = d828 pattern
  rw [s7094, s7000]
  rfl
theorem s7096 (pattern : Twelve) : d842 (change pattern 0 12) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 0 12) else d30 (change pattern 0 12)) = d842 pattern
  rw [s7095, s6983]
  rfl
theorem s7097 (pattern : Twelve) : d843 (change pattern 0 12) = d843 pattern := by
  change (if pattern.f then d825 (change pattern 0 12) else d34 (change pattern 0 12)) = d843 pattern
  rw [s7084, s7000]
  rfl
theorem s7098 (pattern : Twelve) : d855 (change pattern 0 12) = d855 pattern := by
  change (if pattern.e then d843 (change pattern 0 12) else d842 (change pattern 0 12)) = d855 pattern
  rw [s7097, s7096]
  rfl
theorem s7099 (pattern : Twelve) : d815 (change pattern 0 12) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 0 12) else d9 (change pattern 0 12)) = d815 pattern
  rw [s6971, s6972]
  rfl
theorem s7100 (pattern : Twelve) : d820 (change pattern 0 12) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d815 (change pattern 0 12)) = d820 pattern
  rw [s6978, s7099]
  rfl
theorem s7101 (pattern : Twelve) : d829 (change pattern 0 12) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 0 12) else d41 (change pattern 0 12)) = d829 pattern
  rw [s7100, s7029]
  rfl
theorem s7102 (pattern : Twelve) : d844 (change pattern 0 12) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 0 12) else d59 (change pattern 0 12)) = d844 pattern
  rw [s7101, s7023]
  rfl
theorem s7103 (pattern : Twelve) : d830 (change pattern 0 12) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 0 12) else d41 (change pattern 0 12)) = d830 pattern
  rw [s7024, s7029]
  rfl
theorem s7104 (pattern : Twelve) : d821 (change pattern 0 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 0 12) else d25 (change pattern 0 12)) = d821 pattern
  rw [s6992, s7031]
  rfl
theorem s7105 (pattern : Twelve) : d822 (change pattern 0 12) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d21 (change pattern 0 12)) = d822 pattern
  rw [s6978, s6992]
  rfl
theorem s7106 (pattern : Twelve) : d831 (change pattern 0 12) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 0 12) else d821 (change pattern 0 12)) = d831 pattern
  rw [s7105, s7104]
  rfl
theorem s7107 (pattern : Twelve) : d845 (change pattern 0 12) = d845 pattern := by
  change (if pattern.f then d831 (change pattern 0 12) else d830 (change pattern 0 12)) = d845 pattern
  rw [s7106, s7103]
  rfl
theorem s7108 (pattern : Twelve) : d856 (change pattern 0 12) = d856 pattern := by
  change (if pattern.e then d845 (change pattern 0 12) else d844 (change pattern 0 12)) = d856 pattern
  rw [s7107, s7102]
  rfl
theorem s7109 (pattern : Twelve) : d862 (change pattern 0 12) = d862 pattern := by
  change (if pattern.j then d856 (change pattern 0 12) else d855 (change pattern 0 12)) = d862 pattern
  rw [s7108, s7098]
  rfl
theorem s7110 (pattern : Twelve) : d863 (change pattern 0 12) = d863 pattern := by
  change (if pattern.j then d6 (change pattern 0 12) else d854 (change pattern 0 12)) = d863 pattern
  rw [s6978, s7092]
  rfl
theorem s7111 (pattern : Twelve) : d867 (change pattern 0 12) = d867 pattern := by
  change (if pattern.d then d863 (change pattern 0 12) else d862 (change pattern 0 12)) = d867 pattern
  rw [s7110, s7109]
  rfl
theorem s7112 (pattern : Twelve) : d869 (change pattern 0 12) = d869 pattern := by
  change (if pattern.c then d867 (change pattern 0 12) else d861 (change pattern 0 12)) = d869 pattern
  rw [s7111, s7093]
  rfl
theorem s7113 (pattern : Twelve) : d823 (change pattern 0 12) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 0 12) else d17 (change pattern 0 12)) = d823 pattern
  rw [s6969, s6965]
  rfl
theorem s7114 (pattern : Twelve) : d846 (change pattern 0 12) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 0 12) else d823 (change pattern 0 12)) = d846 pattern
  rw [s7084, s7113]
  rfl
theorem s7115 (pattern : Twelve) : d857 (change pattern 0 12) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 0 12) else d838 (change pattern 0 12)) = d857 pattern
  rw [s7114, s7082]
  rfl
theorem s7116 (pattern : Twelve) : d832 (change pattern 0 12) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 0 12) else d34 (change pattern 0 12)) = d832 pattern
  rw [s7050, s7000]
  rfl
theorem s7117 (pattern : Twelve) : d847 (change pattern 0 12) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 0 12) else d56 (change pattern 0 12)) = d847 pattern
  rw [s7116, s7008]
  rfl
theorem s7118 (pattern : Twelve) : d833 (change pattern 0 12) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 0 12) else d34 (change pattern 0 12)) = d833 pattern
  rw [s7022, s7000]
  rfl
theorem s7119 (pattern : Twelve) : d848 (change pattern 0 12) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 0 12) else d833 (change pattern 0 12)) = d848 pattern
  rw [s7084, s7118]
  rfl
theorem s7120 (pattern : Twelve) : d858 (change pattern 0 12) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 0 12) else d847 (change pattern 0 12)) = d858 pattern
  rw [s7119, s7117]
  rfl
theorem s7121 (pattern : Twelve) : d864 (change pattern 0 12) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 0 12) else d857 (change pattern 0 12)) = d864 pattern
  rw [s7120, s7115]
  rfl
theorem s7122 (pattern : Twelve) : d834 (change pattern 0 12) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 0 12) else d34 (change pattern 0 12)) = d834 pattern
  rw [s7058, s7000]
  rfl
theorem s7123 (pattern : Twelve) : d849 (change pattern 0 12) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 0 12) else d30 (change pattern 0 12)) = d849 pattern
  rw [s7122, s6983]
  rfl
theorem s7124 (pattern : Twelve) : d835 (change pattern 0 12) = d835 pattern := by
  change (if pattern.h then d38 (change pattern 0 12) else d34 (change pattern 0 12)) = d835 pattern
  rw [s7021, s7000]
  rfl
theorem s7125 (pattern : Twelve) : d850 (change pattern 0 12) = d850 pattern := by
  change (if pattern.f then d825 (change pattern 0 12) else d835 (change pattern 0 12)) = d850 pattern
  rw [s7084, s7124]
  rfl
theorem s7126 (pattern : Twelve) : d859 (change pattern 0 12) = d859 pattern := by
  change (if pattern.e then d850 (change pattern 0 12) else d849 (change pattern 0 12)) = d859 pattern
  rw [s7125, s7123]
  rfl
theorem s7127 (pattern : Twelve) : d836 (change pattern 0 12) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 0 12) else d41 (change pattern 0 12)) = d836 pattern
  rw [s7064, s7029]
  rfl
theorem s7128 (pattern : Twelve) : d851 (change pattern 0 12) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 0 12) else d59 (change pattern 0 12)) = d851 pattern
  rw [s7127, s7023]
  rfl
theorem s7129 (pattern : Twelve) : d837 (change pattern 0 12) = d837 pattern := by
  change (if pattern.h then d48 (change pattern 0 12) else d41 (change pattern 0 12)) = d837 pattern
  rw [s7067, s7029]
  rfl
theorem s7130 (pattern : Twelve) : d852 (change pattern 0 12) = d852 pattern := by
  change (if pattern.f then d831 (change pattern 0 12) else d837 (change pattern 0 12)) = d852 pattern
  rw [s7106, s7129]
  rfl
theorem s7131 (pattern : Twelve) : d860 (change pattern 0 12) = d860 pattern := by
  change (if pattern.e then d852 (change pattern 0 12) else d851 (change pattern 0 12)) = d860 pattern
  rw [s7130, s7128]
  rfl
theorem s7132 (pattern : Twelve) : d865 (change pattern 0 12) = d865 pattern := by
  change (if pattern.j then d860 (change pattern 0 12) else d859 (change pattern 0 12)) = d865 pattern
  rw [s7131, s7126]
  rfl
theorem s7133 (pattern : Twelve) : d866 (change pattern 0 12) = d866 pattern := by
  change (if pattern.j then d6 (change pattern 0 12) else d858 (change pattern 0 12)) = d866 pattern
  rw [s6978, s7120]
  rfl
theorem s7134 (pattern : Twelve) : d868 (change pattern 0 12) = d868 pattern := by
  change (if pattern.d then d866 (change pattern 0 12) else d865 (change pattern 0 12)) = d868 pattern
  rw [s7133, s7132]
  rfl
theorem s7135 (pattern : Twelve) : d870 (change pattern 0 12) = d870 pattern := by
  change (if pattern.c then d868 (change pattern 0 12) else d864 (change pattern 0 12)) = d870 pattern
  rw [s7134, s7121]
  rfl
theorem s7136 (pattern : Twelve) : d871 (change pattern 0 12) = d871 pattern := by
  change (if pattern.g then d870 (change pattern 0 12) else d869 (change pattern 0 12)) = d871 pattern
  rw [s7135, s7112]
  rfl
theorem s7137 (pattern : Twelve) : d1274 (change pattern 0 12) = d871 pattern := by
  change d871 (change pattern 0 12) = d871 pattern
  exact s7136 pattern
theorem s7138 (pattern : Twelve) : d1275 (change pattern 0 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 0 12) else d7 (change pattern 0 12)) = d1275 pattern
  rw [s6970, s6964]
  rfl
theorem s7139 (pattern : Twelve) : d872 (change pattern 0 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 0 12) else d1 (change pattern 0 12)) = d872 pattern
  rw [s6970, s6962]
  rfl
theorem s7140 (pattern : Twelve) : d1278 (change pattern 0 12) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 0 12) else d1275 (change pattern 0 12)) = d1278 pattern
  rw [s7139, s7138]
  rfl
theorem s7141 (pattern : Twelve) : d1284 (change pattern 0 12) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 0 12) else d1278 (change pattern 0 12)) = d1284 pattern
  rw [s7139, s7140]
  rfl
theorem s7142 (pattern : Twelve) : d1293 (change pattern 0 12) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 0 12) else d17 (change pattern 0 12)) = d1293 pattern
  rw [s7141, s6965]
  rfl
theorem s7143 (pattern : Twelve) : d1294 (change pattern 0 12) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d19 (change pattern 0 12)) = d1294 pattern
  rw [s6978, s6977]
  rfl
theorem s7144 (pattern : Twelve) : d1305 (change pattern 0 12) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 0 12) else d1293 (change pattern 0 12)) = d1305 pattern
  rw [s7143, s7142]
  rfl
theorem s7145 (pattern : Twelve) : d117 (change pattern 0 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 0 12) else d3 (change pattern 0 12)) = d117 pattern
  rw [s6986, s6971]
  rfl
theorem s7146 (pattern : Twelve) : d1276 (change pattern 0 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 0 12) else d9 (change pattern 0 12)) = d1276 pattern
  rw [s7145, s6972]
  rfl
theorem s7147 (pattern : Twelve) : d1279 (change pattern 0 12) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 0 12) else d1275 (change pattern 0 12)) = d1279 pattern
  rw [s7146, s7138]
  rfl
theorem s7148 (pattern : Twelve) : d1280 (change pattern 0 12) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d872 (change pattern 0 12)) = d1280 pattern
  rw [s6978, s7139]
  rfl
theorem s7149 (pattern : Twelve) : d1285 (change pattern 0 12) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 0 12) else d1279 (change pattern 0 12)) = d1285 pattern
  rw [s7148, s7147]
  rfl
theorem s7150 (pattern : Twelve) : d1295 (change pattern 0 12) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 0 12) else d827 (change pattern 0 12)) = d1295 pattern
  rw [s7149, s7090]
  rfl
theorem s7151 (pattern : Twelve) : d1286 (change pattern 0 12) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 0 12) else d817 (change pattern 0 12)) = d1286 pattern
  rw [s6979, s7083]
  rfl
theorem s7152 (pattern : Twelve) : d1296 (change pattern 0 12) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d1286 (change pattern 0 12)) = d1296 pattern
  rw [s6978, s7151]
  rfl
theorem s7153 (pattern : Twelve) : d1306 (change pattern 0 12) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 0 12) else d1295 (change pattern 0 12)) = d1306 pattern
  rw [s7152, s7150]
  rfl
theorem s7154 (pattern : Twelve) : d1313 (change pattern 0 12) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 0 12) else d1305 (change pattern 0 12)) = d1313 pattern
  rw [s7153, s7144]
  rfl
theorem s7155 (pattern : Twelve) : d119 (change pattern 0 12) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 0 12) else d3 (change pattern 0 12)) = d119 pattern
  rw [s7145, s6971]
  rfl
theorem s7156 (pattern : Twelve) : d1281 (change pattern 0 12) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 0 12) else d872 (change pattern 0 12)) = d1281 pattern
  rw [s7155, s7139]
  rfl
theorem s7157 (pattern : Twelve) : d1287 (change pattern 0 12) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 0 12) else d1279 (change pattern 0 12)) = d1287 pattern
  rw [s7156, s7147]
  rfl
theorem s7158 (pattern : Twelve) : d1297 (change pattern 0 12) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 0 12) else d34 (change pattern 0 12)) = d1297 pattern
  rw [s7157, s7000]
  rfl
theorem s7159 (pattern : Twelve) : d1298 (change pattern 0 12) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d817 (change pattern 0 12)) = d1298 pattern
  rw [s6978, s7083]
  rfl
theorem s7160 (pattern : Twelve) : d1307 (change pattern 0 12) = d1307 pattern := by
  change (if pattern.e then d1298 (change pattern 0 12) else d1297 (change pattern 0 12)) = d1307 pattern
  rw [s7159, s7158]
  rfl
theorem s7161 (pattern : Twelve) : d1277 (change pattern 0 12) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 0 12) else d15 (change pattern 0 12)) = d1277 pattern
  rw [s6991, s7027]
  rfl
theorem s7162 (pattern : Twelve) : d1282 (change pattern 0 12) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 0 12) else d1276 (change pattern 0 12)) = d1282 pattern
  rw [s7161, s7146]
  rfl
theorem s7163 (pattern : Twelve) : d125 (change pattern 0 12) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d119 (change pattern 0 12)) = d125 pattern
  rw [s6978, s7155]
  rfl
theorem s7164 (pattern : Twelve) : d1288 (change pattern 0 12) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 0 12) else d1282 (change pattern 0 12)) = d1288 pattern
  rw [s7163, s7162]
  rfl
theorem s7165 (pattern : Twelve) : d1299 (change pattern 0 12) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 0 12) else d830 (change pattern 0 12)) = d1299 pattern
  rw [s7164, s7103]
  rfl
theorem s7166 (pattern : Twelve) : d1289 (change pattern 0 12) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 0 12) else d821 (change pattern 0 12)) = d1289 pattern
  rw [s7032, s7104]
  rfl
theorem s7167 (pattern : Twelve) : d1300 (change pattern 0 12) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d1289 (change pattern 0 12)) = d1300 pattern
  rw [s6978, s7166]
  rfl
theorem s7168 (pattern : Twelve) : d1308 (change pattern 0 12) = d1308 pattern := by
  change (if pattern.e then d1300 (change pattern 0 12) else d1299 (change pattern 0 12)) = d1308 pattern
  rw [s7167, s7165]
  rfl
theorem s7169 (pattern : Twelve) : d1314 (change pattern 0 12) = d1314 pattern := by
  change (if pattern.j then d1308 (change pattern 0 12) else d1307 (change pattern 0 12)) = d1314 pattern
  rw [s7168, s7160]
  rfl
theorem s7170 (pattern : Twelve) : d1315 (change pattern 0 12) = d1315 pattern := by
  change (if pattern.j then d6 (change pattern 0 12) else d1306 (change pattern 0 12)) = d1315 pattern
  rw [s6978, s7153]
  rfl
theorem s7171 (pattern : Twelve) : d1319 (change pattern 0 12) = d1319 pattern := by
  change (if pattern.d then d1315 (change pattern 0 12) else d1314 (change pattern 0 12)) = d1319 pattern
  rw [s7170, s7169]
  rfl
theorem s7172 (pattern : Twelve) : d1321 (change pattern 0 12) = d1321 pattern := by
  change (if pattern.c then d1319 (change pattern 0 12) else d1313 (change pattern 0 12)) = d1321 pattern
  rw [s7171, s7154]
  rfl
theorem s7173 (pattern : Twelve) : d1283 (change pattern 0 12) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 0 12) else d19 (change pattern 0 12)) = d1283 pattern
  rw [s6999, s6977]
  rfl
theorem s7174 (pattern : Twelve) : d1301 (change pattern 0 12) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d1283 (change pattern 0 12)) = d1301 pattern
  rw [s6978, s7173]
  rfl
theorem s7175 (pattern : Twelve) : d1309 (change pattern 0 12) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 0 12) else d1293 (change pattern 0 12)) = d1309 pattern
  rw [s7174, s7142]
  rfl
theorem s7176 (pattern : Twelve) : d1290 (change pattern 0 12) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 0 12) else d817 (change pattern 0 12)) = d1290 pattern
  rw [s7024, s7083]
  rfl
theorem s7177 (pattern : Twelve) : d1302 (change pattern 0 12) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d1290 (change pattern 0 12)) = d1302 pattern
  rw [s6978, s7176]
  rfl
theorem s7178 (pattern : Twelve) : d1310 (change pattern 0 12) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 0 12) else d1295 (change pattern 0 12)) = d1310 pattern
  rw [s7177, s7150]
  rfl
theorem s7179 (pattern : Twelve) : d1316 (change pattern 0 12) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 0 12) else d1309 (change pattern 0 12)) = d1316 pattern
  rw [s7178, s7175]
  rfl
theorem s7180 (pattern : Twelve) : d1291 (change pattern 0 12) = d1291 pattern := by
  change (if pattern.h then d41 (change pattern 0 12) else d817 (change pattern 0 12)) = d1291 pattern
  rw [s7029, s7083]
  rfl
theorem s7181 (pattern : Twelve) : d1303 (change pattern 0 12) = d1303 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d1291 (change pattern 0 12)) = d1303 pattern
  rw [s6978, s7180]
  rfl
theorem s7182 (pattern : Twelve) : d1311 (change pattern 0 12) = d1311 pattern := by
  change (if pattern.e then d1303 (change pattern 0 12) else d1297 (change pattern 0 12)) = d1311 pattern
  rw [s7181, s7158]
  rfl
theorem s7183 (pattern : Twelve) : d1292 (change pattern 0 12) = d1292 pattern := by
  change (if pattern.h then d49 (change pattern 0 12) else d821 (change pattern 0 12)) = d1292 pattern
  rw [s7069, s7104]
  rfl
theorem s7184 (pattern : Twelve) : d1304 (change pattern 0 12) = d1304 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d1292 (change pattern 0 12)) = d1304 pattern
  rw [s6978, s7183]
  rfl
theorem s7185 (pattern : Twelve) : d1312 (change pattern 0 12) = d1312 pattern := by
  change (if pattern.e then d1304 (change pattern 0 12) else d1299 (change pattern 0 12)) = d1312 pattern
  rw [s7184, s7165]
  rfl
theorem s7186 (pattern : Twelve) : d1317 (change pattern 0 12) = d1317 pattern := by
  change (if pattern.j then d1312 (change pattern 0 12) else d1311 (change pattern 0 12)) = d1317 pattern
  rw [s7185, s7182]
  rfl
theorem s7187 (pattern : Twelve) : d1318 (change pattern 0 12) = d1318 pattern := by
  change (if pattern.j then d6 (change pattern 0 12) else d1310 (change pattern 0 12)) = d1318 pattern
  rw [s6978, s7178]
  rfl
theorem s7188 (pattern : Twelve) : d1320 (change pattern 0 12) = d1320 pattern := by
  change (if pattern.d then d1318 (change pattern 0 12) else d1317 (change pattern 0 12)) = d1320 pattern
  rw [s7187, s7186]
  rfl
theorem s7189 (pattern : Twelve) : d1322 (change pattern 0 12) = d1322 pattern := by
  change (if pattern.c then d1320 (change pattern 0 12) else d1316 (change pattern 0 12)) = d1322 pattern
  rw [s7188, s7179]
  rfl
theorem s7190 (pattern : Twelve) : d1323 (change pattern 0 12) = d1323 pattern := by
  change (if pattern.g then d1322 (change pattern 0 12) else d1321 (change pattern 0 12)) = d1323 pattern
  rw [s7189, s7172]
  rfl
theorem s7191 (pattern : Twelve) : d1643 (change pattern 0 12) = d1323 pattern := by
  change d1323 (change pattern 0 12) = d1323 pattern
  exact s7190 pattern
theorem s7192 (pattern : Twelve) : d1324 (change pattern 0 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 0 12) else d11 (change pattern 0 12)) = d1324 pattern
  rw [s7030, s6976]
  rfl
theorem s7193 (pattern : Twelve) : d1649 (change pattern 0 12) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 0 12) else d19 (change pattern 0 12)) = d1649 pattern
  rw [s7192, s6977]
  rfl
theorem s7194 (pattern : Twelve) : d1650 (change pattern 0 12) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d25 (change pattern 0 12)) = d1650 pattern
  rw [s6978, s7031]
  rfl
theorem s7195 (pattern : Twelve) : d1656 (change pattern 0 12) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 0 12) else d1649 (change pattern 0 12)) = d1656 pattern
  rw [s7194, s7193]
  rfl
theorem s7196 (pattern : Twelve) : d1644 (change pattern 0 12) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 0 12) else d1324 (change pattern 0 12)) = d1644 pattern
  rw [s6988, s7192]
  rfl
theorem s7197 (pattern : Twelve) : d1645 (change pattern 0 12) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d1324 (change pattern 0 12)) = d1645 pattern
  rw [s6978, s7192]
  rfl
theorem s7198 (pattern : Twelve) : d1647 (change pattern 0 12) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 0 12) else d1644 (change pattern 0 12)) = d1647 pattern
  rw [s7197, s7196]
  rfl
theorem s7199 (pattern : Twelve) : d1651 (change pattern 0 12) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 0 12) else d1286 (change pattern 0 12)) = d1651 pattern
  rw [s7198, s7151]
  rfl
end NetHack.Sokoban21.Diagram
