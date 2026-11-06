/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions44
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s6750 (pattern : Twelve) : d865 (change pattern 12 1) = d865 pattern := by
  change (if pattern.j then d860 (change pattern 12 1) else d859 (change pattern 12 1)) = d865 pattern
  rw [s6749, s6744]
  rfl
theorem s6751 (pattern : Twelve) : d866 (change pattern 12 1) = d866 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d858 (change pattern 12 1)) = d866 pattern
  rw [s6529, s6738]
  rfl
theorem s6752 (pattern : Twelve) : d868 (change pattern 12 1) = d868 pattern := by
  change (if pattern.d then d866 (change pattern 12 1) else d865 (change pattern 12 1)) = d868 pattern
  rw [s6751, s6750]
  rfl
theorem s6753 (pattern : Twelve) : d870 (change pattern 12 1) = d870 pattern := by
  change (if pattern.c then d868 (change pattern 12 1) else d864 (change pattern 12 1)) = d870 pattern
  rw [s6752, s6739]
  rfl
theorem s6754 (pattern : Twelve) : d871 (change pattern 12 1) = d871 pattern := by
  change (if pattern.g then d870 (change pattern 12 1) else d869 (change pattern 12 1)) = d871 pattern
  rw [s6753, s6730]
  rfl
theorem s6755 (pattern : Twelve) : d872 (change pattern 12 1) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 12 1) else d1 (change pattern 12 1)) = d872 pattern
  rw [s6521, s6513]
  rfl
theorem s6756 (pattern : Twelve) : d874 (change pattern 12 1) = d874 pattern := by
  change (if pattern.i then d872 (change pattern 12 1) else d17 (change pattern 12 1)) = d874 pattern
  rw [s6755, s6516]
  rfl
theorem s6757 (pattern : Twelve) : d875 (change pattern 12 1) = d875 pattern := by
  change (if pattern.i then d872 (change pattern 12 1) else d814 (change pattern 12 1)) = d875 pattern
  rw [s6755, s6697]
  rfl
theorem s6758 (pattern : Twelve) : d882 (change pattern 12 1) = d882 pattern := by
  change (if pattern.h then d875 (change pattern 12 1) else d874 (change pattern 12 1)) = d882 pattern
  rw [s6757, s6756]
  rfl
theorem s6759 (pattern : Twelve) : d890 (change pattern 12 1) = d890 pattern := by
  change (if pattern.f then d882 (change pattern 12 1) else d0 (change pattern 12 1)) = d890 pattern
  rw [s6758, s6512]
  rfl
theorem s6760 (pattern : Twelve) : d876 (change pattern 12 1) = d876 pattern := by
  change (if pattern.i then d21 (change pattern 12 1) else d19 (change pattern 12 1)) = d876 pattern
  rw [s6543, s6528]
  rfl
theorem s6761 (pattern : Twelve) : d883 (change pattern 12 1) = d883 pattern := by
  change (if pattern.h then d42 (change pattern 12 1) else d876 (change pattern 12 1)) = d883 pattern
  rw [s6583, s6760]
  rfl
theorem s6762 (pattern : Twelve) : d891 (change pattern 12 1) = d891 pattern := by
  change (if pattern.f then d883 (change pattern 12 1) else d17 (change pattern 12 1)) = d891 pattern
  rw [s6761, s6516]
  rfl
theorem s6763 (pattern : Twelve) : d898 (change pattern 12 1) = d898 pattern := by
  change (if pattern.e then d891 (change pattern 12 1) else d890 (change pattern 12 1)) = d898 pattern
  rw [s6762, s6759]
  rfl
theorem s6764 (pattern : Twelve) : d877 (change pattern 12 1) = d877 pattern := by
  change (if pattern.i then d815 (change pattern 12 1) else d17 (change pattern 12 1)) = d877 pattern
  rw [s6717, s6516]
  rfl
theorem s6765 (pattern : Twelve) : d884 (change pattern 12 1) = d884 pattern := by
  change (if pattern.h then d818 (change pattern 12 1) else d877 (change pattern 12 1)) = d884 pattern
  rw [s6705, s6764]
  rfl
theorem s6766 (pattern : Twelve) : d892 (change pattern 12 1) = d892 pattern := by
  change (if pattern.f then d884 (change pattern 12 1) else d56 (change pattern 12 1)) = d892 pattern
  rw [s6765, s6559]
  rfl
theorem s6767 (pattern : Twelve) : d893 (change pattern 12 1) = d893 pattern := by
  change (if pattern.f then d883 (change pattern 12 1) else d827 (change pattern 12 1)) = d893 pattern
  rw [s6761, s6708]
  rfl
theorem s6768 (pattern : Twelve) : d899 (change pattern 12 1) = d899 pattern := by
  change (if pattern.e then d893 (change pattern 12 1) else d892 (change pattern 12 1)) = d899 pattern
  rw [s6767, s6766]
  rfl
theorem s6769 (pattern : Twelve) : d902 (change pattern 12 1) = d902 pattern := by
  change (if pattern.j then d899 (change pattern 12 1) else d898 (change pattern 12 1)) = d902 pattern
  rw [s6768, s6763]
  rfl
theorem s6770 (pattern : Twelve) : d878 (change pattern 12 1) = d878 pattern := by
  change (if pattern.i then d24 (change pattern 12 1) else d814 (change pattern 12 1)) = d878 pattern
  rw [s6579, s6697]
  rfl
theorem s6771 (pattern : Twelve) : d885 (change pattern 12 1) = d885 pattern := by
  change (if pattern.h then d878 (change pattern 12 1) else d877 (change pattern 12 1)) = d885 pattern
  rw [s6770, s6764]
  rfl
theorem s6772 (pattern : Twelve) : d894 (change pattern 12 1) = d894 pattern := by
  change (if pattern.f then d885 (change pattern 12 1) else d30 (change pattern 12 1)) = d894 pattern
  rw [s6771, s6534]
  rfl
theorem s6773 (pattern : Twelve) : d879 (change pattern 12 1) = d879 pattern := by
  change (if pattern.i then d119 (change pattern 12 1) else d17 (change pattern 12 1)) = d879 pattern
  rw [s6653, s6516]
  rfl
theorem s6774 (pattern : Twelve) : d886 (change pattern 12 1) = d886 pattern := by
  change (if pattern.h then d879 (change pattern 12 1) else d34 (change pattern 12 1)) = d886 pattern
  rw [s6773, s6551]
  rfl
theorem s6775 (pattern : Twelve) : d895 (change pattern 12 1) = d895 pattern := by
  change (if pattern.f then d883 (change pattern 12 1) else d886 (change pattern 12 1)) = d895 pattern
  rw [s6761, s6774]
  rfl
theorem s6776 (pattern : Twelve) : d900 (change pattern 12 1) = d900 pattern := by
  change (if pattern.e then d895 (change pattern 12 1) else d894 (change pattern 12 1)) = d900 pattern
  rw [s6775, s6772]
  rfl
theorem s6777 (pattern : Twelve) : d873 (change pattern 12 1) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 12 1) else d117 (change pattern 12 1)) = d873 pattern
  rw [s6578, s6652]
  rfl
theorem s6778 (pattern : Twelve) : d880 (change pattern 12 1) = d880 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d873 (change pattern 12 1)) = d880 pattern
  rw [s6529, s6777]
  rfl
theorem s6779 (pattern : Twelve) : d887 (change pattern 12 1) = d887 pattern := by
  change (if pattern.h then d880 (change pattern 12 1) else d127 (change pattern 12 1)) = d887 pattern
  rw [s6778, s6659]
  rfl
theorem s6780 (pattern : Twelve) : d896 (change pattern 12 1) = d896 pattern := by
  change (if pattern.f then d887 (change pattern 12 1) else d59 (change pattern 12 1)) = d896 pattern
  rw [s6779, s6574]
  rfl
theorem s6781 (pattern : Twelve) : d881 (change pattern 12 1) = d881 pattern := by
  change (if pattern.i then d118 (change pattern 12 1) else d23 (change pattern 12 1)) = d881 pattern
  rw [s6650, s6550]
  rfl
theorem s6782 (pattern : Twelve) : d888 (change pattern 12 1) = d888 pattern := by
  change (if pattern.h then d125 (change pattern 12 1) else d881 (change pattern 12 1)) = d888 pattern
  rw [s6654, s6781]
  rfl
theorem s6783 (pattern : Twelve) : d889 (change pattern 12 1) = d889 pattern := by
  change (if pattern.h then d6 (change pattern 12 1) else d42 (change pattern 12 1)) = d889 pattern
  rw [s6529, s6583]
  rfl
theorem s6784 (pattern : Twelve) : d897 (change pattern 12 1) = d897 pattern := by
  change (if pattern.f then d889 (change pattern 12 1) else d888 (change pattern 12 1)) = d897 pattern
  rw [s6783, s6782]
  rfl
theorem s6785 (pattern : Twelve) : d901 (change pattern 12 1) = d901 pattern := by
  change (if pattern.e then d897 (change pattern 12 1) else d896 (change pattern 12 1)) = d901 pattern
  rw [s6784, s6780]
  rfl
theorem s6786 (pattern : Twelve) : d903 (change pattern 12 1) = d903 pattern := by
  change (if pattern.j then d901 (change pattern 12 1) else d900 (change pattern 12 1)) = d903 pattern
  rw [s6785, s6776]
  rfl
theorem s6787 (pattern : Twelve) : d904 (change pattern 12 1) = d904 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d899 (change pattern 12 1)) = d904 pattern
  rw [s6529, s6768]
  rfl
theorem s6788 (pattern : Twelve) : d905 (change pattern 12 1) = d905 pattern := by
  change (if pattern.d then d904 (change pattern 12 1) else d903 (change pattern 12 1)) = d905 pattern
  rw [s6787, s6786]
  rfl
theorem s6789 (pattern : Twelve) : d906 (change pattern 12 1) = d906 pattern := by
  change (if pattern.c then d905 (change pattern 12 1) else d902 (change pattern 12 1)) = d906 pattern
  rw [s6788, s6769]
  rfl
theorem s6790 (pattern : Twelve) : d1247 (change pattern 12 1) = d1247 pattern := by
  change (if pattern.i then d3 (change pattern 12 1) else d815 (change pattern 12 1)) = d1247 pattern
  rw [s6522, s6717]
  rfl
theorem s6791 (pattern : Twelve) : d1249 (change pattern 12 1) = d1249 pattern := by
  change (if pattern.h then d1247 (change pattern 12 1) else d779 (change pattern 12 1)) = d1249 pattern
  rw [s6790, s6669]
  rfl
theorem s6792 (pattern : Twelve) : d1253 (change pattern 12 1) = d1253 pattern := by
  change (if pattern.f then d1249 (change pattern 12 1) else d2 (change pattern 12 1)) = d1253 pattern
  rw [s6791, s6520]
  rfl
theorem s6793 (pattern : Twelve) : d1248 (change pattern 12 1) = d1248 pattern := by
  change (if pattern.i then d4 (change pattern 12 1) else d23 (change pattern 12 1)) = d1248 pattern
  rw [s6537, s6550]
  rfl
theorem s6794 (pattern : Twelve) : d1254 (change pattern 12 1) = d1254 pattern := by
  change (if pattern.f then d831 (change pattern 12 1) else d1248 (change pattern 12 1)) = d1254 pattern
  rw [s6724, s6793]
  rfl
theorem s6795 (pattern : Twelve) : d1258 (change pattern 12 1) = d1258 pattern := by
  change (if pattern.e then d1254 (change pattern 12 1) else d1253 (change pattern 12 1)) = d1258 pattern
  rw [s6794, s6792]
  rfl
theorem s6796 (pattern : Twelve) : d1261 (change pattern 12 1) = d1261 pattern := by
  change (if pattern.j then d860 (change pattern 12 1) else d1258 (change pattern 12 1)) = d1261 pattern
  rw [s6749, s6795]
  rfl
theorem s6797 (pattern : Twelve) : d1250 (change pattern 12 1) = d1250 pattern := by
  change (if pattern.h then d780 (change pattern 12 1) else d41 (change pattern 12 1)) = d1250 pattern
  rw [s6680, s6580]
  rfl
theorem s6798 (pattern : Twelve) : d1255 (change pattern 12 1) = d1255 pattern := by
  change (if pattern.f then d1250 (change pattern 12 1) else d38 (change pattern 12 1)) = d1255 pattern
  rw [s6797, s6572]
  rfl
theorem s6799 (pattern : Twelve) : d1259 (change pattern 12 1) = d1259 pattern := by
  change (if pattern.e then d852 (change pattern 12 1) else d1255 (change pattern 12 1)) = d1259 pattern
  rw [s6748, s6798]
  rfl
theorem s6800 (pattern : Twelve) : d1251 (change pattern 12 1) = d1251 pattern := by
  change (if pattern.h then d781 (change pattern 12 1) else d49 (change pattern 12 1)) = d1251 pattern
  rw [s6684, s6620]
  rfl
theorem s6801 (pattern : Twelve) : d1256 (change pattern 12 1) = d1256 pattern := by
  change (if pattern.f then d1251 (change pattern 12 1) else d48 (change pattern 12 1)) = d1256 pattern
  rw [s6800, s6618]
  rfl
theorem s6802 (pattern : Twelve) : d1252 (change pattern 12 1) = d1252 pattern := by
  change (if pattern.h then d6 (change pattern 12 1) else d822 (change pattern 12 1)) = d1252 pattern
  rw [s6529, s6723]
  rfl
theorem s6803 (pattern : Twelve) : d1257 (change pattern 12 1) = d1257 pattern := by
  change (if pattern.f then d1252 (change pattern 12 1) else d787 (change pattern 12 1)) = d1257 pattern
  rw [s6802, s6688]
  rfl
theorem s6804 (pattern : Twelve) : d1260 (change pattern 12 1) = d1260 pattern := by
  change (if pattern.e then d1257 (change pattern 12 1) else d1256 (change pattern 12 1)) = d1260 pattern
  rw [s6803, s6801]
  rfl
theorem s6805 (pattern : Twelve) : d1262 (change pattern 12 1) = d1262 pattern := by
  change (if pattern.j then d1260 (change pattern 12 1) else d1259 (change pattern 12 1)) = d1262 pattern
  rw [s6804, s6799]
  rfl
theorem s6806 (pattern : Twelve) : d1263 (change pattern 12 1) = d1263 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d860 (change pattern 12 1)) = d1263 pattern
  rw [s6529, s6749]
  rfl
theorem s6807 (pattern : Twelve) : d1264 (change pattern 12 1) = d1264 pattern := by
  change (if pattern.d then d1263 (change pattern 12 1) else d1262 (change pattern 12 1)) = d1264 pattern
  rw [s6806, s6805]
  rfl
theorem s6808 (pattern : Twelve) : d1265 (change pattern 12 1) = d1265 pattern := by
  change (if pattern.c then d1264 (change pattern 12 1) else d1261 (change pattern 12 1)) = d1265 pattern
  rw [s6807, s6796]
  rfl
theorem s6809 (pattern : Twelve) : d1266 (change pattern 12 1) = d1266 pattern := by
  change (if pattern.g then d1265 (change pattern 12 1) else d906 (change pattern 12 1)) = d1266 pattern
  rw [s6808, s6789]
  rfl
theorem s6810 (pattern : Twelve) : d1267 (change pattern 12 1) = d1267 pattern := by
  change (if pattern.a then d1266 (change pattern 12 1) else d871 (change pattern 12 1)) = d1267 pattern
  rw [s6809, s6754]
  rfl
theorem s6811 (pattern : Twelve) : d1275 (change pattern 12 1) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 12 1) else d7 (change pattern 12 1)) = d1275 pattern
  rw [s6521, s6515]
  rfl
theorem s6812 (pattern : Twelve) : d1278 (change pattern 12 1) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 12 1) else d1275 (change pattern 12 1)) = d1278 pattern
  rw [s6755, s6811]
  rfl
theorem s6813 (pattern : Twelve) : d1284 (change pattern 12 1) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 12 1) else d1278 (change pattern 12 1)) = d1284 pattern
  rw [s6755, s6812]
  rfl
theorem s6814 (pattern : Twelve) : d1293 (change pattern 12 1) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 12 1) else d17 (change pattern 12 1)) = d1293 pattern
  rw [s6813, s6516]
  rfl
theorem s6815 (pattern : Twelve) : d1294 (change pattern 12 1) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d19 (change pattern 12 1)) = d1294 pattern
  rw [s6529, s6528]
  rfl
theorem s6816 (pattern : Twelve) : d1305 (change pattern 12 1) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 12 1) else d1293 (change pattern 12 1)) = d1305 pattern
  rw [s6815, s6814]
  rfl
theorem s6817 (pattern : Twelve) : d1276 (change pattern 12 1) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 12 1) else d9 (change pattern 12 1)) = d1276 pattern
  rw [s6652, s6523]
  rfl
theorem s6818 (pattern : Twelve) : d1279 (change pattern 12 1) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 12 1) else d1275 (change pattern 12 1)) = d1279 pattern
  rw [s6817, s6811]
  rfl
theorem s6819 (pattern : Twelve) : d1280 (change pattern 12 1) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d872 (change pattern 12 1)) = d1280 pattern
  rw [s6529, s6755]
  rfl
theorem s6820 (pattern : Twelve) : d1285 (change pattern 12 1) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 12 1) else d1279 (change pattern 12 1)) = d1285 pattern
  rw [s6819, s6818]
  rfl
theorem s6821 (pattern : Twelve) : d1295 (change pattern 12 1) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 12 1) else d827 (change pattern 12 1)) = d1295 pattern
  rw [s6820, s6708]
  rfl
theorem s6822 (pattern : Twelve) : d1286 (change pattern 12 1) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 12 1) else d817 (change pattern 12 1)) = d1286 pattern
  rw [s6530, s6701]
  rfl
theorem s6823 (pattern : Twelve) : d1296 (change pattern 12 1) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1286 (change pattern 12 1)) = d1296 pattern
  rw [s6529, s6822]
  rfl
theorem s6824 (pattern : Twelve) : d1306 (change pattern 12 1) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 12 1) else d1295 (change pattern 12 1)) = d1306 pattern
  rw [s6823, s6821]
  rfl
theorem s6825 (pattern : Twelve) : d1313 (change pattern 12 1) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 12 1) else d1305 (change pattern 12 1)) = d1313 pattern
  rw [s6824, s6816]
  rfl
theorem s6826 (pattern : Twelve) : d1281 (change pattern 12 1) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 12 1) else d872 (change pattern 12 1)) = d1281 pattern
  rw [s6653, s6755]
  rfl
theorem s6827 (pattern : Twelve) : d1287 (change pattern 12 1) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 12 1) else d1279 (change pattern 12 1)) = d1287 pattern
  rw [s6826, s6818]
  rfl
theorem s6828 (pattern : Twelve) : d1297 (change pattern 12 1) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 12 1) else d34 (change pattern 12 1)) = d1297 pattern
  rw [s6827, s6551]
  rfl
theorem s6829 (pattern : Twelve) : d1298 (change pattern 12 1) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d817 (change pattern 12 1)) = d1298 pattern
  rw [s6529, s6701]
  rfl
theorem s6830 (pattern : Twelve) : d1307 (change pattern 12 1) = d1307 pattern := by
  change (if pattern.e then d1298 (change pattern 12 1) else d1297 (change pattern 12 1)) = d1307 pattern
  rw [s6829, s6828]
  rfl
theorem s6831 (pattern : Twelve) : d1277 (change pattern 12 1) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 12 1) else d15 (change pattern 12 1)) = d1277 pattern
  rw [s6542, s6578]
  rfl
theorem s6832 (pattern : Twelve) : d1282 (change pattern 12 1) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 12 1) else d1276 (change pattern 12 1)) = d1282 pattern
  rw [s6831, s6817]
  rfl
theorem s6833 (pattern : Twelve) : d1288 (change pattern 12 1) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 12 1) else d1282 (change pattern 12 1)) = d1288 pattern
  rw [s6654, s6832]
  rfl
theorem s6834 (pattern : Twelve) : d1299 (change pattern 12 1) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 12 1) else d830 (change pattern 12 1)) = d1299 pattern
  rw [s6833, s6721]
  rfl
theorem s6835 (pattern : Twelve) : d1289 (change pattern 12 1) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 12 1) else d821 (change pattern 12 1)) = d1289 pattern
  rw [s6583, s6722]
  rfl
theorem s6836 (pattern : Twelve) : d1300 (change pattern 12 1) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1289 (change pattern 12 1)) = d1300 pattern
  rw [s6529, s6835]
  rfl
theorem s6837 (pattern : Twelve) : d1308 (change pattern 12 1) = d1308 pattern := by
  change (if pattern.e then d1300 (change pattern 12 1) else d1299 (change pattern 12 1)) = d1308 pattern
  rw [s6836, s6834]
  rfl
theorem s6838 (pattern : Twelve) : d1314 (change pattern 12 1) = d1314 pattern := by
  change (if pattern.j then d1308 (change pattern 12 1) else d1307 (change pattern 12 1)) = d1314 pattern
  rw [s6837, s6830]
  rfl
theorem s6839 (pattern : Twelve) : d1315 (change pattern 12 1) = d1315 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d1306 (change pattern 12 1)) = d1315 pattern
  rw [s6529, s6824]
  rfl
theorem s6840 (pattern : Twelve) : d1319 (change pattern 12 1) = d1319 pattern := by
  change (if pattern.d then d1315 (change pattern 12 1) else d1314 (change pattern 12 1)) = d1319 pattern
  rw [s6839, s6838]
  rfl
theorem s6841 (pattern : Twelve) : d1321 (change pattern 12 1) = d1321 pattern := by
  change (if pattern.c then d1319 (change pattern 12 1) else d1313 (change pattern 12 1)) = d1321 pattern
  rw [s6840, s6825]
  rfl
theorem s6842 (pattern : Twelve) : d1283 (change pattern 12 1) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 12 1) else d19 (change pattern 12 1)) = d1283 pattern
  rw [s6550, s6528]
  rfl
theorem s6843 (pattern : Twelve) : d1301 (change pattern 12 1) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1283 (change pattern 12 1)) = d1301 pattern
  rw [s6529, s6842]
  rfl
theorem s6844 (pattern : Twelve) : d1309 (change pattern 12 1) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 12 1) else d1293 (change pattern 12 1)) = d1309 pattern
  rw [s6843, s6814]
  rfl
theorem s6845 (pattern : Twelve) : d1290 (change pattern 12 1) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 12 1) else d817 (change pattern 12 1)) = d1290 pattern
  rw [s6575, s6701]
  rfl
theorem s6846 (pattern : Twelve) : d1302 (change pattern 12 1) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1290 (change pattern 12 1)) = d1302 pattern
  rw [s6529, s6845]
  rfl
theorem s6847 (pattern : Twelve) : d1310 (change pattern 12 1) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 12 1) else d1295 (change pattern 12 1)) = d1310 pattern
  rw [s6846, s6821]
  rfl
theorem s6848 (pattern : Twelve) : d1316 (change pattern 12 1) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 12 1) else d1309 (change pattern 12 1)) = d1316 pattern
  rw [s6847, s6844]
  rfl
theorem s6849 (pattern : Twelve) : d1291 (change pattern 12 1) = d1291 pattern := by
  change (if pattern.h then d41 (change pattern 12 1) else d817 (change pattern 12 1)) = d1291 pattern
  rw [s6580, s6701]
  rfl
theorem s6850 (pattern : Twelve) : d1303 (change pattern 12 1) = d1303 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1291 (change pattern 12 1)) = d1303 pattern
  rw [s6529, s6849]
  rfl
theorem s6851 (pattern : Twelve) : d1311 (change pattern 12 1) = d1311 pattern := by
  change (if pattern.e then d1303 (change pattern 12 1) else d1297 (change pattern 12 1)) = d1311 pattern
  rw [s6850, s6828]
  rfl
theorem s6852 (pattern : Twelve) : d1292 (change pattern 12 1) = d1292 pattern := by
  change (if pattern.h then d49 (change pattern 12 1) else d821 (change pattern 12 1)) = d1292 pattern
  rw [s6620, s6722]
  rfl
theorem s6853 (pattern : Twelve) : d1304 (change pattern 12 1) = d1304 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1292 (change pattern 12 1)) = d1304 pattern
  rw [s6529, s6852]
  rfl
theorem s6854 (pattern : Twelve) : d1312 (change pattern 12 1) = d1312 pattern := by
  change (if pattern.e then d1304 (change pattern 12 1) else d1299 (change pattern 12 1)) = d1312 pattern
  rw [s6853, s6834]
  rfl
theorem s6855 (pattern : Twelve) : d1317 (change pattern 12 1) = d1317 pattern := by
  change (if pattern.j then d1312 (change pattern 12 1) else d1311 (change pattern 12 1)) = d1317 pattern
  rw [s6854, s6851]
  rfl
theorem s6856 (pattern : Twelve) : d1318 (change pattern 12 1) = d1318 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d1310 (change pattern 12 1)) = d1318 pattern
  rw [s6529, s6847]
  rfl
theorem s6857 (pattern : Twelve) : d1320 (change pattern 12 1) = d1320 pattern := by
  change (if pattern.d then d1318 (change pattern 12 1) else d1317 (change pattern 12 1)) = d1320 pattern
  rw [s6856, s6855]
  rfl
theorem s6858 (pattern : Twelve) : d1322 (change pattern 12 1) = d1322 pattern := by
  change (if pattern.c then d1320 (change pattern 12 1) else d1316 (change pattern 12 1)) = d1322 pattern
  rw [s6857, s6848]
  rfl
theorem s6859 (pattern : Twelve) : d1323 (change pattern 12 1) = d1323 pattern := by
  change (if pattern.g then d1322 (change pattern 12 1) else d1321 (change pattern 12 1)) = d1323 pattern
  rw [s6858, s6841]
  rfl
theorem s6860 (pattern : Twelve) : d1324 (change pattern 12 1) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 12 1) else d11 (change pattern 12 1)) = d1324 pattern
  rw [s6581, s6527]
  rfl
theorem s6861 (pattern : Twelve) : d1325 (change pattern 12 1) = d1325 pattern := by
  change (if pattern.i then d1324 (change pattern 12 1) else d1275 (change pattern 12 1)) = d1325 pattern
  rw [s6860, s6811]
  rfl
theorem s6862 (pattern : Twelve) : d1326 (change pattern 12 1) = d1326 pattern := by
  change (if pattern.i then d1324 (change pattern 12 1) else d872 (change pattern 12 1)) = d1326 pattern
  rw [s6860, s6755]
  rfl
theorem s6863 (pattern : Twelve) : d1333 (change pattern 12 1) = d1333 pattern := by
  change (if pattern.h then d1326 (change pattern 12 1) else d1325 (change pattern 12 1)) = d1333 pattern
  rw [s6862, s6861]
  rfl
theorem s6864 (pattern : Twelve) : d1339 (change pattern 12 1) = d1339 pattern := by
  change (if pattern.f then d1333 (change pattern 12 1) else d17 (change pattern 12 1)) = d1339 pattern
  rw [s6863, s6516]
  rfl
theorem s6865 (pattern : Twelve) : d1345 (change pattern 12 1) = d1345 pattern := by
  change (if pattern.e then d1294 (change pattern 12 1) else d1339 (change pattern 12 1)) = d1345 pattern
  rw [s6815, s6864]
  rfl
theorem s6866 (pattern : Twelve) : d1327 (change pattern 12 1) = d1327 pattern := by
  change (if pattern.i then d119 (change pattern 12 1) else d1275 (change pattern 12 1)) = d1327 pattern
  rw [s6653, s6811]
  rfl
theorem s6867 (pattern : Twelve) : d1334 (change pattern 12 1) = d1334 pattern := by
  change (if pattern.h then d1280 (change pattern 12 1) else d1327 (change pattern 12 1)) = d1334 pattern
  rw [s6819, s6866]
  rfl
theorem s6868 (pattern : Twelve) : d1340 (change pattern 12 1) = d1340 pattern := by
  change (if pattern.f then d1334 (change pattern 12 1) else d827 (change pattern 12 1)) = d1340 pattern
  rw [s6867, s6708]
  rfl
theorem s6869 (pattern : Twelve) : d1346 (change pattern 12 1) = d1346 pattern := by
  change (if pattern.e then d1296 (change pattern 12 1) else d1340 (change pattern 12 1)) = d1346 pattern
  rw [s6823, s6868]
  rfl
theorem s6870 (pattern : Twelve) : d1349 (change pattern 12 1) = d1349 pattern := by
  change (if pattern.j then d1346 (change pattern 12 1) else d1345 (change pattern 12 1)) = d1349 pattern
  rw [s6869, s6865]
  rfl
theorem s6871 (pattern : Twelve) : d1328 (change pattern 12 1) = d1328 pattern := by
  change (if pattern.i then d1277 (change pattern 12 1) else d872 (change pattern 12 1)) = d1328 pattern
  rw [s6831, s6755]
  rfl
theorem s6872 (pattern : Twelve) : d1335 (change pattern 12 1) = d1335 pattern := by
  change (if pattern.h then d1328 (change pattern 12 1) else d1327 (change pattern 12 1)) = d1335 pattern
  rw [s6871, s6866]
  rfl
theorem s6873 (pattern : Twelve) : d1341 (change pattern 12 1) = d1341 pattern := by
  change (if pattern.f then d1335 (change pattern 12 1) else d34 (change pattern 12 1)) = d1341 pattern
  rw [s6872, s6551]
  rfl
theorem s6874 (pattern : Twelve) : d1329 (change pattern 12 1) = d1329 pattern := by
  change (if pattern.i then d20 (change pattern 12 1) else d19 (change pattern 12 1)) = d1329 pattern
  rw [s6539, s6528]
  rfl
theorem s6875 (pattern : Twelve) : d1336 (change pattern 12 1) = d1336 pattern := by
  change (if pattern.h then d1329 (change pattern 12 1) else d817 (change pattern 12 1)) = d1336 pattern
  rw [s6874, s6701]
  rfl
theorem s6876 (pattern : Twelve) : d1342 (change pattern 12 1) = d1342 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1336 (change pattern 12 1)) = d1342 pattern
  rw [s6529, s6875]
  rfl
theorem s6877 (pattern : Twelve) : d1347 (change pattern 12 1) = d1347 pattern := by
  change (if pattern.e then d1342 (change pattern 12 1) else d1341 (change pattern 12 1)) = d1347 pattern
  rw [s6876, s6873]
  rfl
theorem s6878 (pattern : Twelve) : d1330 (change pattern 12 1) = d1330 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d1276 (change pattern 12 1)) = d1330 pattern
  rw [s6529, s6817]
  rfl
theorem s6879 (pattern : Twelve) : d1331 (change pattern 12 1) = d1331 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d1277 (change pattern 12 1)) = d1331 pattern
  rw [s6529, s6831]
  rfl
theorem s6880 (pattern : Twelve) : d1337 (change pattern 12 1) = d1337 pattern := by
  change (if pattern.h then d1331 (change pattern 12 1) else d1330 (change pattern 12 1)) = d1337 pattern
  rw [s6879, s6878]
  rfl
theorem s6881 (pattern : Twelve) : d1343 (change pattern 12 1) = d1343 pattern := by
  change (if pattern.f then d1337 (change pattern 12 1) else d830 (change pattern 12 1)) = d1343 pattern
  rw [s6880, s6721]
  rfl
theorem s6882 (pattern : Twelve) : d1332 (change pattern 12 1) = d1332 pattern := by
  change (if pattern.i then d22 (change pattern 12 1) else d25 (change pattern 12 1)) = d1332 pattern
  rw [s6547, s6582]
  rfl
theorem s6883 (pattern : Twelve) : d1338 (change pattern 12 1) = d1338 pattern := by
  change (if pattern.h then d128 (change pattern 12 1) else d1332 (change pattern 12 1)) = d1338 pattern
  rw [s6660, s6882]
  rfl
theorem s6884 (pattern : Twelve) : d1344 (change pattern 12 1) = d1344 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1338 (change pattern 12 1)) = d1344 pattern
  rw [s6529, s6883]
  rfl
theorem s6885 (pattern : Twelve) : d1348 (change pattern 12 1) = d1348 pattern := by
  change (if pattern.e then d1344 (change pattern 12 1) else d1343 (change pattern 12 1)) = d1348 pattern
  rw [s6884, s6881]
  rfl
theorem s6886 (pattern : Twelve) : d1350 (change pattern 12 1) = d1350 pattern := by
  change (if pattern.j then d1348 (change pattern 12 1) else d1347 (change pattern 12 1)) = d1350 pattern
  rw [s6885, s6877]
  rfl
theorem s6887 (pattern : Twelve) : d1351 (change pattern 12 1) = d1351 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d1346 (change pattern 12 1)) = d1351 pattern
  rw [s6529, s6869]
  rfl
theorem s6888 (pattern : Twelve) : d1352 (change pattern 12 1) = d1352 pattern := by
  change (if pattern.d then d1351 (change pattern 12 1) else d1350 (change pattern 12 1)) = d1352 pattern
  rw [s6887, s6886]
  rfl
theorem s6889 (pattern : Twelve) : d1353 (change pattern 12 1) = d1353 pattern := by
  change (if pattern.c then d1352 (change pattern 12 1) else d1349 (change pattern 12 1)) = d1353 pattern
  rw [s6888, s6870]
  rfl
theorem s6890 (pattern : Twelve) : d1616 (change pattern 12 1) = d1616 pattern := by
  change (if pattern.i then d119 (change pattern 12 1) else d1276 (change pattern 12 1)) = d1616 pattern
  rw [s6653, s6817]
  rfl
theorem s6891 (pattern : Twelve) : d1619 (change pattern 12 1) = d1619 pattern := by
  change (if pattern.h then d119 (change pattern 12 1) else d1616 (change pattern 12 1)) = d1619 pattern
  rw [s6653, s6890]
  rfl
theorem s6892 (pattern : Twelve) : d1622 (change pattern 12 1) = d1622 pattern := by
  change (if pattern.f then d1619 (change pattern 12 1) else d23 (change pattern 12 1)) = d1622 pattern
  rw [s6891, s6550]
  rfl
theorem s6893 (pattern : Twelve) : d1617 (change pattern 12 1) = d1617 pattern := by
  change (if pattern.i then d24 (change pattern 12 1) else d25 (change pattern 12 1)) = d1617 pattern
  rw [s6579, s6582]
  rfl
theorem s6894 (pattern : Twelve) : d1623 (change pattern 12 1) = d1623 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1617 (change pattern 12 1)) = d1623 pattern
  rw [s6529, s6893]
  rfl
theorem s6895 (pattern : Twelve) : d1627 (change pattern 12 1) = d1627 pattern := by
  change (if pattern.e then d1623 (change pattern 12 1) else d1622 (change pattern 12 1)) = d1627 pattern
  rw [s6894, s6892]
  rfl
theorem s6896 (pattern : Twelve) : d1630 (change pattern 12 1) = d1630 pattern := by
  change (if pattern.j then d1312 (change pattern 12 1) else d1627 (change pattern 12 1)) = d1630 pattern
  rw [s6854, s6895]
  rfl
theorem s6897 (pattern : Twelve) : d1618 (change pattern 12 1) = d1618 pattern := by
  change (if pattern.i then d118 (change pattern 12 1) else d119 (change pattern 12 1)) = d1618 pattern
  rw [s6650, s6653]
  rfl
theorem s6898 (pattern : Twelve) : d1620 (change pattern 12 1) = d1620 pattern := by
  change (if pattern.h then d1618 (change pattern 12 1) else d1282 (change pattern 12 1)) = d1620 pattern
  rw [s6897, s6832]
  rfl
theorem s6899 (pattern : Twelve) : d1624 (change pattern 12 1) = d1624 pattern := by
  change (if pattern.f then d1620 (change pattern 12 1) else d41 (change pattern 12 1)) = d1624 pattern
  rw [s6898, s6580]
  rfl
end NetHack.Sokoban21.Diagram
