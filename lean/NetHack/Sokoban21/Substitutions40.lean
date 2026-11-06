/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions39
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s6000 (pattern : Twelve) : d791 (change pattern 12 6) = d791 pattern := by
  change (if pattern.f then d784 (change pattern 12 6) else d38 (change pattern 12 6)) = d791 pattern
  rw [s5999, s5960]
  rfl
theorem s6001 (pattern : Twelve) : d796 (change pattern 12 6) = d796 pattern := by
  change (if pattern.e then d90 (change pattern 12 6) else d791 (change pattern 12 6)) = d796 pattern
  rw [s5975, s6000]
  rfl
theorem s6002 (pattern : Twelve) : d781 (change pattern 12 6) = d781 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d5 (change pattern 12 6)) = d781 pattern
  rw [s5921, s5926]
  rfl
theorem s6003 (pattern : Twelve) : d785 (change pattern 12 6) = d785 pattern := by
  change (if pattern.h then d781 (change pattern 12 6) else d48 (change pattern 12 6)) = d785 pattern
  rw [s6002, s5968]
  rfl
theorem s6004 (pattern : Twelve) : d792 (change pattern 12 6) = d792 pattern := by
  change (if pattern.f then d785 (change pattern 12 6) else d48 (change pattern 12 6)) = d792 pattern
  rw [s6003, s5968]
  rfl
theorem s6005 (pattern : Twelve) : d786 (change pattern 12 6) = d786 pattern := by
  change (if pattern.h then d6 (change pattern 12 6) else d48 (change pattern 12 6)) = d786 pattern
  rw [s5921, s5968]
  rfl
theorem s6006 (pattern : Twelve) : d787 (change pattern 12 6) = d787 pattern := by
  change (if pattern.h then d6 (change pattern 12 6) else d49 (change pattern 12 6)) = d787 pattern
  rw [s5921, s5973]
  rfl
theorem s6007 (pattern : Twelve) : d793 (change pattern 12 6) = d793 pattern := by
  change (if pattern.f then d787 (change pattern 12 6) else d786 (change pattern 12 6)) = d793 pattern
  rw [s6006, s6005]
  rfl
theorem s6008 (pattern : Twelve) : d797 (change pattern 12 6) = d797 pattern := by
  change (if pattern.e then d793 (change pattern 12 6) else d792 (change pattern 12 6)) = d797 pattern
  rw [s6007, s6004]
  rfl
theorem s6009 (pattern : Twelve) : d800 (change pattern 12 6) = d800 pattern := by
  change (if pattern.j then d797 (change pattern 12 6) else d796 (change pattern 12 6)) = d800 pattern
  rw [s6008, s6001]
  rfl
theorem s6010 (pattern : Twelve) : d801 (change pattern 12 6) = d801 pattern := by
  change (if pattern.j then d6 (change pattern 12 6) else d101 (change pattern 12 6)) = d801 pattern
  rw [s5921, s5976]
  rfl
theorem s6011 (pattern : Twelve) : d803 (change pattern 12 6) = d803 pattern := by
  change (if pattern.d then d801 (change pattern 12 6) else d800 (change pattern 12 6)) = d803 pattern
  rw [s6010, s6009]
  rfl
theorem s6012 (pattern : Twelve) : d804 (change pattern 12 6) = d804 pattern := by
  change (if pattern.c then d803 (change pattern 12 6) else d802 (change pattern 12 6)) = d804 pattern
  rw [s6011, s5997]
  rfl
theorem s6013 (pattern : Twelve) : d805 (change pattern 12 6) = d804 pattern := by
  change d804 (change pattern 12 6) = d804 pattern
  exact s6012 pattern
theorem s6014 (pattern : Twelve) : d806 (change pattern 12 6) = d3237 pattern := by
  change (if pattern.a then d805 (change pattern 12 6) else d116 (change pattern 12 6)) = d3237 pattern
  rw [s6013, s5981]
  rfl
theorem s6015 (pattern : Twelve) : d814 (change pattern 12 6) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 12 6) else d7 (change pattern 12 6)) = d814 pattern
  rw [s5905, s5907]
  rfl
theorem s6016 (pattern : Twelve) : d816 (change pattern 12 6) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 12 6) else d814 (change pattern 12 6)) = d816 pattern
  rw [s5905, s6015]
  rfl
theorem s6017 (pattern : Twelve) : d824 (change pattern 12 6) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 12 6) else d27 (change pattern 12 6)) = d824 pattern
  rw [s6016, s5909]
  rfl
theorem s6018 (pattern : Twelve) : d838 (change pattern 12 6) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 12 6) else d0 (change pattern 12 6)) = d838 pattern
  rw [s6017, s5904]
  rfl
theorem s6019 (pattern : Twelve) : d823 (change pattern 12 6) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 12 6) else d17 (change pattern 12 6)) = d823 pattern
  rw [s5912, s5908]
  rfl
theorem s6020 (pattern : Twelve) : d817 (change pattern 12 6) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 12 6) else d19 (change pattern 12 6)) = d817 pattern
  rw [s5987, s5920]
  rfl
theorem s6021 (pattern : Twelve) : d825 (change pattern 12 6) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 12 6) else d817 (change pattern 12 6)) = d825 pattern
  rw [s5988, s6020]
  rfl
theorem s6022 (pattern : Twelve) : d846 (change pattern 12 6) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 12 6) else d823 (change pattern 12 6)) = d846 pattern
  rw [s6021, s6019]
  rfl
theorem s6023 (pattern : Twelve) : d857 (change pattern 12 6) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 12 6) else d838 (change pattern 12 6)) = d857 pattern
  rw [s6022, s6018]
  rfl
theorem s6024 (pattern : Twelve) : d832 (change pattern 12 6) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 12 6) else d34 (change pattern 12 6)) = d832 pattern
  rw [s5948, s5917]
  rfl
theorem s6025 (pattern : Twelve) : d847 (change pattern 12 6) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 12 6) else d56 (change pattern 12 6)) = d847 pattern
  rw [s6024, s5947]
  rfl
theorem s6026 (pattern : Twelve) : d833 (change pattern 12 6) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 12 6) else d34 (change pattern 12 6)) = d833 pattern
  rw [s5951, s5917]
  rfl
theorem s6027 (pattern : Twelve) : d848 (change pattern 12 6) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 12 6) else d833 (change pattern 12 6)) = d848 pattern
  rw [s6021, s6026]
  rfl
theorem s6028 (pattern : Twelve) : d858 (change pattern 12 6) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 12 6) else d847 (change pattern 12 6)) = d858 pattern
  rw [s6027, s6025]
  rfl
theorem s6029 (pattern : Twelve) : d864 (change pattern 12 6) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 12 6) else d857 (change pattern 12 6)) = d864 pattern
  rw [s6028, s6023]
  rfl
theorem s6030 (pattern : Twelve) : d834 (change pattern 12 6) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 12 6) else d34 (change pattern 12 6)) = d834 pattern
  rw [s5957, s5917]
  rfl
theorem s6031 (pattern : Twelve) : d849 (change pattern 12 6) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 12 6) else d30 (change pattern 12 6)) = d849 pattern
  rw [s6030, s5913]
  rfl
theorem s6032 (pattern : Twelve) : d835 (change pattern 12 6) = d835 pattern := by
  change (if pattern.h then d38 (change pattern 12 6) else d34 (change pattern 12 6)) = d835 pattern
  rw [s5960, s5917]
  rfl
theorem s6033 (pattern : Twelve) : d850 (change pattern 12 6) = d850 pattern := by
  change (if pattern.f then d825 (change pattern 12 6) else d835 (change pattern 12 6)) = d850 pattern
  rw [s6021, s6032]
  rfl
theorem s6034 (pattern : Twelve) : d859 (change pattern 12 6) = d859 pattern := by
  change (if pattern.e then d850 (change pattern 12 6) else d849 (change pattern 12 6)) = d859 pattern
  rw [s6033, s6031]
  rfl
theorem s6035 (pattern : Twelve) : d836 (change pattern 12 6) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 12 6) else d41 (change pattern 12 6)) = d836 pattern
  rw [s5965, s5972]
  rfl
theorem s6036 (pattern : Twelve) : d851 (change pattern 12 6) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 12 6) else d59 (change pattern 12 6)) = d851 pattern
  rw [s6035, s5964]
  rfl
theorem s6037 (pattern : Twelve) : d837 (change pattern 12 6) = d837 pattern := by
  change (if pattern.h then d48 (change pattern 12 6) else d41 (change pattern 12 6)) = d837 pattern
  rw [s5968, s5972]
  rfl
theorem s6038 (pattern : Twelve) : d821 (change pattern 12 6) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 12 6) else d25 (change pattern 12 6)) = d821 pattern
  rw [s5934, s5987]
  rfl
theorem s6039 (pattern : Twelve) : d822 (change pattern 12 6) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d21 (change pattern 12 6)) = d822 pattern
  rw [s5921, s5934]
  rfl
theorem s6040 (pattern : Twelve) : d831 (change pattern 12 6) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 12 6) else d821 (change pattern 12 6)) = d831 pattern
  rw [s6039, s6038]
  rfl
theorem s6041 (pattern : Twelve) : d852 (change pattern 12 6) = d852 pattern := by
  change (if pattern.f then d831 (change pattern 12 6) else d837 (change pattern 12 6)) = d852 pattern
  rw [s6040, s6037]
  rfl
theorem s6042 (pattern : Twelve) : d860 (change pattern 12 6) = d860 pattern := by
  change (if pattern.e then d852 (change pattern 12 6) else d851 (change pattern 12 6)) = d860 pattern
  rw [s6041, s6036]
  rfl
theorem s6043 (pattern : Twelve) : d865 (change pattern 12 6) = d865 pattern := by
  change (if pattern.j then d860 (change pattern 12 6) else d859 (change pattern 12 6)) = d865 pattern
  rw [s6042, s6034]
  rfl
theorem s6044 (pattern : Twelve) : d866 (change pattern 12 6) = d866 pattern := by
  change (if pattern.j then d6 (change pattern 12 6) else d858 (change pattern 12 6)) = d866 pattern
  rw [s5921, s6028]
  rfl
theorem s6045 (pattern : Twelve) : d868 (change pattern 12 6) = d868 pattern := by
  change (if pattern.d then d866 (change pattern 12 6) else d865 (change pattern 12 6)) = d868 pattern
  rw [s6044, s6043]
  rfl
theorem s6046 (pattern : Twelve) : d870 (change pattern 12 6) = d870 pattern := by
  change (if pattern.c then d868 (change pattern 12 6) else d864 (change pattern 12 6)) = d870 pattern
  rw [s6045, s6029]
  rfl
theorem s6047 (pattern : Twelve) : d871 (change pattern 12 6) = d870 pattern := by
  change d870 (change pattern 12 6) = d870 pattern
  exact s6046 pattern
theorem s6048 (pattern : Twelve) : d815 (change pattern 12 6) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 12 6) else d9 (change pattern 12 6)) = d815 pattern
  rw [s5914, s5915]
  rfl
theorem s6049 (pattern : Twelve) : d1247 (change pattern 12 6) = d1247 pattern := by
  change (if pattern.i then d3 (change pattern 12 6) else d815 (change pattern 12 6)) = d1247 pattern
  rw [s5914, s6048]
  rfl
theorem s6050 (pattern : Twelve) : d1249 (change pattern 12 6) = d1249 pattern := by
  change (if pattern.h then d1247 (change pattern 12 6) else d779 (change pattern 12 6)) = d1249 pattern
  rw [s6049, s5983]
  rfl
theorem s6051 (pattern : Twelve) : d1253 (change pattern 12 6) = d1253 pattern := by
  change (if pattern.f then d1249 (change pattern 12 6) else d2 (change pattern 12 6)) = d1253 pattern
  rw [s6050, s5912]
  rfl
theorem s6052 (pattern : Twelve) : d1248 (change pattern 12 6) = d1248 pattern := by
  change (if pattern.i then d4 (change pattern 12 6) else d23 (change pattern 12 6)) = d1248 pattern
  rw [s5928, s5916]
  rfl
theorem s6053 (pattern : Twelve) : d1254 (change pattern 12 6) = d1254 pattern := by
  change (if pattern.f then d831 (change pattern 12 6) else d1248 (change pattern 12 6)) = d1254 pattern
  rw [s6040, s6052]
  rfl
theorem s6054 (pattern : Twelve) : d1258 (change pattern 12 6) = d1258 pattern := by
  change (if pattern.e then d1254 (change pattern 12 6) else d1253 (change pattern 12 6)) = d1258 pattern
  rw [s6053, s6051]
  rfl
theorem s6055 (pattern : Twelve) : d1261 (change pattern 12 6) = d1261 pattern := by
  change (if pattern.j then d860 (change pattern 12 6) else d1258 (change pattern 12 6)) = d1261 pattern
  rw [s6042, s6054]
  rfl
theorem s6056 (pattern : Twelve) : d1250 (change pattern 12 6) = d1250 pattern := by
  change (if pattern.h then d780 (change pattern 12 6) else d41 (change pattern 12 6)) = d1250 pattern
  rw [s5998, s5972]
  rfl
theorem s6057 (pattern : Twelve) : d1255 (change pattern 12 6) = d1255 pattern := by
  change (if pattern.f then d1250 (change pattern 12 6) else d38 (change pattern 12 6)) = d1255 pattern
  rw [s6056, s5960]
  rfl
theorem s6058 (pattern : Twelve) : d1259 (change pattern 12 6) = d1259 pattern := by
  change (if pattern.e then d852 (change pattern 12 6) else d1255 (change pattern 12 6)) = d1259 pattern
  rw [s6041, s6057]
  rfl
theorem s6059 (pattern : Twelve) : d1251 (change pattern 12 6) = d1251 pattern := by
  change (if pattern.h then d781 (change pattern 12 6) else d49 (change pattern 12 6)) = d1251 pattern
  rw [s6002, s5973]
  rfl
theorem s6060 (pattern : Twelve) : d1256 (change pattern 12 6) = d1256 pattern := by
  change (if pattern.f then d1251 (change pattern 12 6) else d48 (change pattern 12 6)) = d1256 pattern
  rw [s6059, s5968]
  rfl
theorem s6061 (pattern : Twelve) : d1252 (change pattern 12 6) = d1252 pattern := by
  change (if pattern.h then d6 (change pattern 12 6) else d822 (change pattern 12 6)) = d1252 pattern
  rw [s5921, s6039]
  rfl
theorem s6062 (pattern : Twelve) : d1257 (change pattern 12 6) = d1257 pattern := by
  change (if pattern.f then d1252 (change pattern 12 6) else d787 (change pattern 12 6)) = d1257 pattern
  rw [s6061, s6006]
  rfl
theorem s6063 (pattern : Twelve) : d1260 (change pattern 12 6) = d1260 pattern := by
  change (if pattern.e then d1257 (change pattern 12 6) else d1256 (change pattern 12 6)) = d1260 pattern
  rw [s6062, s6060]
  rfl
theorem s6064 (pattern : Twelve) : d1262 (change pattern 12 6) = d1262 pattern := by
  change (if pattern.j then d1260 (change pattern 12 6) else d1259 (change pattern 12 6)) = d1262 pattern
  rw [s6063, s6058]
  rfl
theorem s6065 (pattern : Twelve) : d1263 (change pattern 12 6) = d1263 pattern := by
  change (if pattern.j then d6 (change pattern 12 6) else d860 (change pattern 12 6)) = d1263 pattern
  rw [s5921, s6042]
  rfl
theorem s6066 (pattern : Twelve) : d1264 (change pattern 12 6) = d1264 pattern := by
  change (if pattern.d then d1263 (change pattern 12 6) else d1262 (change pattern 12 6)) = d1264 pattern
  rw [s6065, s6064]
  rfl
theorem s6067 (pattern : Twelve) : d1265 (change pattern 12 6) = d1265 pattern := by
  change (if pattern.c then d1264 (change pattern 12 6) else d1261 (change pattern 12 6)) = d1265 pattern
  rw [s6066, s6055]
  rfl
theorem s6068 (pattern : Twelve) : d1266 (change pattern 12 6) = d1265 pattern := by
  change d1265 (change pattern 12 6) = d1265 pattern
  exact s6067 pattern
theorem s6069 (pattern : Twelve) : d1267 (change pattern 12 6) = d3238 pattern := by
  change (if pattern.a then d1266 (change pattern 12 6) else d871 (change pattern 12 6)) = d3238 pattern
  rw [s6068, s6047]
  rfl
theorem s6070 (pattern : Twelve) : d8 (change pattern 12 6) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 12 6) else d1 (change pattern 12 6)) = d8 pattern
  rw [s5912, s5905]
  rfl
theorem s6071 (pattern : Twelve) : d1275 (change pattern 12 6) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 12 6) else d7 (change pattern 12 6)) = d1275 pattern
  rw [s6070, s5907]
  rfl
theorem s6072 (pattern : Twelve) : d872 (change pattern 12 6) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 12 6) else d1 (change pattern 12 6)) = d872 pattern
  rw [s6070, s5905]
  rfl
theorem s6073 (pattern : Twelve) : d1278 (change pattern 12 6) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 12 6) else d1275 (change pattern 12 6)) = d1278 pattern
  rw [s6072, s6071]
  rfl
theorem s6074 (pattern : Twelve) : d1284 (change pattern 12 6) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 12 6) else d1278 (change pattern 12 6)) = d1284 pattern
  rw [s6072, s6073]
  rfl
theorem s6075 (pattern : Twelve) : d1293 (change pattern 12 6) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 12 6) else d17 (change pattern 12 6)) = d1293 pattern
  rw [s6074, s5908]
  rfl
theorem s6076 (pattern : Twelve) : d1283 (change pattern 12 6) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 12 6) else d19 (change pattern 12 6)) = d1283 pattern
  rw [s5916, s5920]
  rfl
theorem s6077 (pattern : Twelve) : d1301 (change pattern 12 6) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d1283 (change pattern 12 6)) = d1301 pattern
  rw [s5921, s6076]
  rfl
theorem s6078 (pattern : Twelve) : d1309 (change pattern 12 6) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 12 6) else d1293 (change pattern 12 6)) = d1309 pattern
  rw [s6077, s6075]
  rfl
theorem s6079 (pattern : Twelve) : d36 (change pattern 12 6) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d17 (change pattern 12 6)) = d36 pattern
  rw [s5921, s5908]
  rfl
theorem s6080 (pattern : Twelve) : d827 (change pattern 12 6) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 12 6) else d34 (change pattern 12 6)) = d827 pattern
  rw [s6079, s5917]
  rfl
theorem s6081 (pattern : Twelve) : d117 (change pattern 12 6) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 12 6) else d3 (change pattern 12 6)) = d117 pattern
  rw [s5928, s5914]
  rfl
theorem s6082 (pattern : Twelve) : d1276 (change pattern 12 6) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 12 6) else d9 (change pattern 12 6)) = d1276 pattern
  rw [s6081, s5915]
  rfl
theorem s6083 (pattern : Twelve) : d1279 (change pattern 12 6) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 12 6) else d1275 (change pattern 12 6)) = d1279 pattern
  rw [s6082, s6071]
  rfl
theorem s6084 (pattern : Twelve) : d1280 (change pattern 12 6) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d872 (change pattern 12 6)) = d1280 pattern
  rw [s5921, s6072]
  rfl
theorem s6085 (pattern : Twelve) : d1285 (change pattern 12 6) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 12 6) else d1279 (change pattern 12 6)) = d1285 pattern
  rw [s6084, s6083]
  rfl
theorem s6086 (pattern : Twelve) : d1295 (change pattern 12 6) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 12 6) else d827 (change pattern 12 6)) = d1295 pattern
  rw [s6085, s6080]
  rfl
theorem s6087 (pattern : Twelve) : d1290 (change pattern 12 6) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 12 6) else d817 (change pattern 12 6)) = d1290 pattern
  rw [s5941, s6020]
  rfl
theorem s6088 (pattern : Twelve) : d1302 (change pattern 12 6) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d1290 (change pattern 12 6)) = d1302 pattern
  rw [s5921, s6087]
  rfl
theorem s6089 (pattern : Twelve) : d1310 (change pattern 12 6) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 12 6) else d1295 (change pattern 12 6)) = d1310 pattern
  rw [s6088, s6086]
  rfl
theorem s6090 (pattern : Twelve) : d1316 (change pattern 12 6) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 12 6) else d1309 (change pattern 12 6)) = d1316 pattern
  rw [s6089, s6078]
  rfl
theorem s6091 (pattern : Twelve) : d119 (change pattern 12 6) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 12 6) else d3 (change pattern 12 6)) = d119 pattern
  rw [s6081, s5914]
  rfl
theorem s6092 (pattern : Twelve) : d1281 (change pattern 12 6) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 12 6) else d872 (change pattern 12 6)) = d1281 pattern
  rw [s6091, s6072]
  rfl
theorem s6093 (pattern : Twelve) : d1287 (change pattern 12 6) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 12 6) else d1279 (change pattern 12 6)) = d1287 pattern
  rw [s6092, s6083]
  rfl
theorem s6094 (pattern : Twelve) : d1297 (change pattern 12 6) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 12 6) else d34 (change pattern 12 6)) = d1297 pattern
  rw [s6093, s5917]
  rfl
theorem s6095 (pattern : Twelve) : d1291 (change pattern 12 6) = d1291 pattern := by
  change (if pattern.h then d41 (change pattern 12 6) else d817 (change pattern 12 6)) = d1291 pattern
  rw [s5972, s6020]
  rfl
theorem s6096 (pattern : Twelve) : d1303 (change pattern 12 6) = d1303 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d1291 (change pattern 12 6)) = d1303 pattern
  rw [s5921, s6095]
  rfl
theorem s6097 (pattern : Twelve) : d1311 (change pattern 12 6) = d1311 pattern := by
  change (if pattern.e then d1303 (change pattern 12 6) else d1297 (change pattern 12 6)) = d1311 pattern
  rw [s6096, s6094]
  rfl
theorem s6098 (pattern : Twelve) : d830 (change pattern 12 6) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 12 6) else d41 (change pattern 12 6)) = d830 pattern
  rw [s5941, s5972]
  rfl
theorem s6099 (pattern : Twelve) : d1277 (change pattern 12 6) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 12 6) else d15 (change pattern 12 6)) = d1277 pattern
  rw [s5933, s5970]
  rfl
theorem s6100 (pattern : Twelve) : d1282 (change pattern 12 6) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 12 6) else d1276 (change pattern 12 6)) = d1282 pattern
  rw [s6099, s6082]
  rfl
theorem s6101 (pattern : Twelve) : d125 (change pattern 12 6) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d119 (change pattern 12 6)) = d125 pattern
  rw [s5921, s6091]
  rfl
theorem s6102 (pattern : Twelve) : d1288 (change pattern 12 6) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 12 6) else d1282 (change pattern 12 6)) = d1288 pattern
  rw [s6101, s6100]
  rfl
theorem s6103 (pattern : Twelve) : d1299 (change pattern 12 6) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 12 6) else d830 (change pattern 12 6)) = d1299 pattern
  rw [s6102, s6098]
  rfl
theorem s6104 (pattern : Twelve) : d1292 (change pattern 12 6) = d1292 pattern := by
  change (if pattern.h then d49 (change pattern 12 6) else d821 (change pattern 12 6)) = d1292 pattern
  rw [s5973, s6038]
  rfl
theorem s6105 (pattern : Twelve) : d1304 (change pattern 12 6) = d1304 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d1292 (change pattern 12 6)) = d1304 pattern
  rw [s5921, s6104]
  rfl
theorem s6106 (pattern : Twelve) : d1312 (change pattern 12 6) = d1312 pattern := by
  change (if pattern.e then d1304 (change pattern 12 6) else d1299 (change pattern 12 6)) = d1312 pattern
  rw [s6105, s6103]
  rfl
theorem s6107 (pattern : Twelve) : d1317 (change pattern 12 6) = d1317 pattern := by
  change (if pattern.j then d1312 (change pattern 12 6) else d1311 (change pattern 12 6)) = d1317 pattern
  rw [s6106, s6097]
  rfl
theorem s6108 (pattern : Twelve) : d1318 (change pattern 12 6) = d1318 pattern := by
  change (if pattern.j then d6 (change pattern 12 6) else d1310 (change pattern 12 6)) = d1318 pattern
  rw [s5921, s6089]
  rfl
theorem s6109 (pattern : Twelve) : d1320 (change pattern 12 6) = d1320 pattern := by
  change (if pattern.d then d1318 (change pattern 12 6) else d1317 (change pattern 12 6)) = d1320 pattern
  rw [s6108, s6107]
  rfl
theorem s6110 (pattern : Twelve) : d1322 (change pattern 12 6) = d1322 pattern := by
  change (if pattern.c then d1320 (change pattern 12 6) else d1316 (change pattern 12 6)) = d1322 pattern
  rw [s6109, s6090]
  rfl
theorem s6111 (pattern : Twelve) : d1323 (change pattern 12 6) = d1322 pattern := by
  change d1322 (change pattern 12 6) = d1322 pattern
  exact s6110 pattern
theorem s6112 (pattern : Twelve) : d1616 (change pattern 12 6) = d1616 pattern := by
  change (if pattern.i then d119 (change pattern 12 6) else d1276 (change pattern 12 6)) = d1616 pattern
  rw [s6091, s6082]
  rfl
theorem s6113 (pattern : Twelve) : d1619 (change pattern 12 6) = d1619 pattern := by
  change (if pattern.h then d119 (change pattern 12 6) else d1616 (change pattern 12 6)) = d1619 pattern
  rw [s6091, s6112]
  rfl
theorem s6114 (pattern : Twelve) : d1622 (change pattern 12 6) = d1622 pattern := by
  change (if pattern.f then d1619 (change pattern 12 6) else d23 (change pattern 12 6)) = d1622 pattern
  rw [s6113, s5916]
  rfl
theorem s6115 (pattern : Twelve) : d1617 (change pattern 12 6) = d1617 pattern := by
  change (if pattern.i then d24 (change pattern 12 6) else d25 (change pattern 12 6)) = d1617 pattern
  rw [s5971, s5987]
  rfl
theorem s6116 (pattern : Twelve) : d1623 (change pattern 12 6) = d1623 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d1617 (change pattern 12 6)) = d1623 pattern
  rw [s5921, s6115]
  rfl
theorem s6117 (pattern : Twelve) : d1627 (change pattern 12 6) = d1627 pattern := by
  change (if pattern.e then d1623 (change pattern 12 6) else d1622 (change pattern 12 6)) = d1627 pattern
  rw [s6116, s6114]
  rfl
theorem s6118 (pattern : Twelve) : d1630 (change pattern 12 6) = d1630 pattern := by
  change (if pattern.j then d1312 (change pattern 12 6) else d1627 (change pattern 12 6)) = d1630 pattern
  rw [s6106, s6117]
  rfl
theorem s6119 (pattern : Twelve) : d118 (change pattern 12 6) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 12 6) else d5 (change pattern 12 6)) = d118 pattern
  rw [s5933, s5926]
  rfl
theorem s6120 (pattern : Twelve) : d1618 (change pattern 12 6) = d1618 pattern := by
  change (if pattern.i then d118 (change pattern 12 6) else d119 (change pattern 12 6)) = d1618 pattern
  rw [s6119, s6091]
  rfl
theorem s6121 (pattern : Twelve) : d1620 (change pattern 12 6) = d1620 pattern := by
  change (if pattern.h then d1618 (change pattern 12 6) else d1282 (change pattern 12 6)) = d1620 pattern
  rw [s6120, s6100]
  rfl
theorem s6122 (pattern : Twelve) : d1624 (change pattern 12 6) = d1624 pattern := by
  change (if pattern.f then d1620 (change pattern 12 6) else d41 (change pattern 12 6)) = d1624 pattern
  rw [s6121, s5972]
  rfl
theorem s6123 (pattern : Twelve) : d1628 (change pattern 12 6) = d1628 pattern := by
  change (if pattern.e then d1304 (change pattern 12 6) else d1624 (change pattern 12 6)) = d1628 pattern
  rw [s6105, s6122]
  rfl
theorem s6124 (pattern : Twelve) : d1331 (change pattern 12 6) = d1331 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d1277 (change pattern 12 6)) = d1331 pattern
  rw [s5921, s6099]
  rfl
theorem s6125 (pattern : Twelve) : d182 (change pattern 12 6) = d182 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d118 (change pattern 12 6)) = d182 pattern
  rw [s5921, s6119]
  rfl
theorem s6126 (pattern : Twelve) : d1621 (change pattern 12 6) = d1621 pattern := by
  change (if pattern.h then d182 (change pattern 12 6) else d1331 (change pattern 12 6)) = d1621 pattern
  rw [s6125, s6124]
  rfl
theorem s6127 (pattern : Twelve) : d1625 (change pattern 12 6) = d1625 pattern := by
  change (if pattern.f then d1621 (change pattern 12 6) else d49 (change pattern 12 6)) = d1625 pattern
  rw [s6126, s5973]
  rfl
theorem s6128 (pattern : Twelve) : d1626 (change pattern 12 6) = d1626 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d1252 (change pattern 12 6)) = d1626 pattern
  rw [s5921, s6061]
  rfl
theorem s6129 (pattern : Twelve) : d1629 (change pattern 12 6) = d1629 pattern := by
  change (if pattern.e then d1626 (change pattern 12 6) else d1625 (change pattern 12 6)) = d1629 pattern
  rw [s6128, s6127]
  rfl
theorem s6130 (pattern : Twelve) : d1631 (change pattern 12 6) = d1631 pattern := by
  change (if pattern.j then d1629 (change pattern 12 6) else d1628 (change pattern 12 6)) = d1631 pattern
  rw [s6129, s6123]
  rfl
theorem s6131 (pattern : Twelve) : d1632 (change pattern 12 6) = d1632 pattern := by
  change (if pattern.j then d6 (change pattern 12 6) else d1312 (change pattern 12 6)) = d1632 pattern
  rw [s5921, s6106]
  rfl
theorem s6132 (pattern : Twelve) : d1633 (change pattern 12 6) = d1633 pattern := by
  change (if pattern.d then d1632 (change pattern 12 6) else d1631 (change pattern 12 6)) = d1633 pattern
  rw [s6131, s6130]
  rfl
theorem s6133 (pattern : Twelve) : d1634 (change pattern 12 6) = d1634 pattern := by
  change (if pattern.c then d1633 (change pattern 12 6) else d1630 (change pattern 12 6)) = d1634 pattern
  rw [s6132, s6118]
  rfl
theorem s6134 (pattern : Twelve) : d1635 (change pattern 12 6) = d1634 pattern := by
  change d1634 (change pattern 12 6) = d1634 pattern
  exact s6133 pattern
theorem s6135 (pattern : Twelve) : d1636 (change pattern 12 6) = d3239 pattern := by
  change (if pattern.a then d1635 (change pattern 12 6) else d1323 (change pattern 12 6)) = d3239 pattern
  rw [s6134, s6111]
  rfl
theorem s6136 (pattern : Twelve) : d1324 (change pattern 12 6) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 12 6) else d11 (change pattern 12 6)) = d1324 pattern
  rw [s5986, s5919]
  rfl
theorem s6137 (pattern : Twelve) : d1649 (change pattern 12 6) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 12 6) else d19 (change pattern 12 6)) = d1649 pattern
  rw [s6136, s5920]
  rfl
theorem s6138 (pattern : Twelve) : d1650 (change pattern 12 6) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d25 (change pattern 12 6)) = d1650 pattern
  rw [s5921, s5987]
  rfl
theorem s6139 (pattern : Twelve) : d1656 (change pattern 12 6) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 12 6) else d1649 (change pattern 12 6)) = d1656 pattern
  rw [s6138, s6137]
  rfl
theorem s6140 (pattern : Twelve) : d1286 (change pattern 12 6) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 12 6) else d817 (change pattern 12 6)) = d1286 pattern
  rw [s5922, s6020]
  rfl
theorem s6141 (pattern : Twelve) : d1644 (change pattern 12 6) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 12 6) else d1324 (change pattern 12 6)) = d1644 pattern
  rw [s5930, s6136]
  rfl
theorem s6142 (pattern : Twelve) : d1645 (change pattern 12 6) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d1324 (change pattern 12 6)) = d1645 pattern
  rw [s5921, s6136]
  rfl
theorem s6143 (pattern : Twelve) : d1647 (change pattern 12 6) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 12 6) else d1644 (change pattern 12 6)) = d1647 pattern
  rw [s6142, s6141]
  rfl
theorem s6144 (pattern : Twelve) : d1651 (change pattern 12 6) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 12 6) else d1286 (change pattern 12 6)) = d1651 pattern
  rw [s6143, s6140]
  rfl
theorem s6145 (pattern : Twelve) : d1289 (change pattern 12 6) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 12 6) else d821 (change pattern 12 6)) = d1289 pattern
  rw [s5988, s6038]
  rfl
theorem s6146 (pattern : Twelve) : d1300 (change pattern 12 6) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d1289 (change pattern 12 6)) = d1300 pattern
  rw [s5921, s6145]
  rfl
theorem s6147 (pattern : Twelve) : d1657 (change pattern 12 6) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 12 6) else d1651 (change pattern 12 6)) = d1657 pattern
  rw [s6146, s6144]
  rfl
theorem s6148 (pattern : Twelve) : d1660 (change pattern 12 6) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 12 6) else d1656 (change pattern 12 6)) = d1660 pattern
  rw [s6147, s6139]
  rfl
theorem s6149 (pattern : Twelve) : d1652 (change pattern 12 6) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 12 6) else d817 (change pattern 12 6)) = d1652 pattern
  rw [s6141, s6020]
  rfl
end NetHack.Sokoban21.Diagram
