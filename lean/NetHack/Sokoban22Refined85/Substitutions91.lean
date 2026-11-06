/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions90
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub10920 (p : Pattern) : d2143 (change p 204 (some 182)) = d5921 p := by
  change (if p 163 then d1910 (change p 204 (some 182)) else d2142 (change p 204 (some 182))) = d5921 p
  rw [sub10684, sub10919]
  rfl
theorem sub10921 (p : Pattern) : d2144 (change p 204 (some 182)) = d5922 p := by
  change (if p 162 then d2120 (change p 204 (some 182)) else d2143 (change p 204 (some 182))) = d5922 p
  rw [sub10897, sub10920]
  rfl
theorem sub10922 (p : Pattern) : d2145 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d528 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10493]
  simp only [ite_self]
theorem sub10923 (p : Pattern) : d2146 (change p 204 (some 182)) = d5923 p := by
  change (if p 161 then d2145 (change p 204 (some 182)) else d2144 (change p 204 (some 182))) = d5923 p
  rw [sub10922, sub10921]
  rfl
theorem sub10924 (p : Pattern) : d2147 (change p 204 (some 182)) = d6013 p := by
  change (if p 160 then d2146 (change p 204 (some 182)) else d2141 (change p 204 (some 182))) = d6013 p
  rw [sub10923, sub10918]
  rfl
theorem sub10925 (p : Pattern) : d2148 (change p 204 (some 182)) = d6014 p := by
  change (if p 141 then d2147 (change p 204 (some 182)) else d2123 (change p 204 (some 182))) = d6014 p
  rw [sub10924, sub10900]
  rfl
theorem sub10926 (p : Pattern) : d2149 (change p 204 (some 182)) = d6015 p := by
  change (if p 163 then d1959 (change p 204 (some 182)) else d1953 (change p 204 (some 182))) = d6015 p
  rw [sub10733, sub10727]
  rfl
theorem sub10927 (p : Pattern) : d2150 (change p 204 (some 182)) = d6016 p := by
  change (if p 163 then d1756 (change p 204 (some 182)) else d1973 (change p 204 (some 182))) = d6016 p
  rw [sub10514, sub10748]
  rfl
theorem sub10928 (p : Pattern) : d2151 (change p 204 (some 182)) = d6017 p := by
  change (if p 162 then d2150 (change p 204 (some 182)) else d2149 (change p 204 (some 182))) = d6017 p
  rw [sub10927, sub10926]
  rfl
theorem sub10929 (p : Pattern) : d2152 (change p 204 (some 182)) = d6018 p := by
  change (if p 161 then d1983 (change p 204 (some 182)) else d2151 (change p 204 (some 182))) = d6018 p
  rw [sub10758, sub10928]
  rfl
theorem sub10930 (p : Pattern) : d2153 (change p 204 (some 182)) = d6019 p := by
  change (if p 160 then d1987 (change p 204 (some 182)) else d2152 (change p 204 (some 182))) = d6019 p
  rw [sub10762, sub10929]
  rfl
theorem sub10931 (p : Pattern) : d2154 (change p 204 (some 182)) = d2154 p := by
  change (if p 247 then d11 (change p 204 (some 182)) else d3 (change p 204 (some 182))) = d2154 p
  rw [sub10445, sub10636]
  rfl
theorem sub10932 (p : Pattern) : d2155 (change p 204 (some 182)) = d2155 p := by
  change (if p 246 then d39 (change p 204 (some 182)) else d2154 (change p 204 (some 182))) = d2155 p
  rw [sub10447, sub10931]
  rfl
theorem sub10933 (p : Pattern) : d2156 (change p 204 (some 182)) = d2156 p := by
  change (if p 225 then d2155 (change p 204 (some 182)) else d1895 (change p 204 (some 182))) = d2156 p
  rw [sub10932, sub10667]
  rfl
theorem sub10934 (p : Pattern) : d2157 (change p 204 (some 182)) = d2157 p := by
  change (if p 224 then d2156 (change p 204 (some 182)) else d1893 (change p 204 (some 182))) = d2157 p
  rw [sub10933, sub10665]
  rfl
theorem sub10935 (p : Pattern) : d2158 (change p 204 (some 182)) = d2157 p := by
  change d2157 (change p 204 (some 182)) = d2157 p
  exact sub10934 p
theorem sub10936 (p : Pattern) : d2159 (change p 204 (some 182)) = d2157 p := by
  change d2158 (change p 204 (some 182)) = d2157 p
  exact sub10935 p
theorem sub10937 (p : Pattern) : d2160 (change p 204 (some 182)) = d6020 p := by
  change (if p 163 then d1973 (change p 204 (some 182)) else d2159 (change p 204 (some 182))) = d6020 p
  rw [sub10748, sub10936]
  rfl
theorem sub10938 (p : Pattern) : d2161 (change p 204 (some 182)) = d6021 p := by
  change (if p 162 then d2098 (change p 204 (some 182)) else d2160 (change p 204 (some 182))) = d6021 p
  rw [sub10875, sub10937]
  rfl
theorem sub10939 (p : Pattern) : d2162 (change p 204 (some 182)) = d6022 p := by
  change (if p 161 then d1986 (change p 204 (some 182)) else d2161 (change p 204 (some 182))) = d6022 p
  rw [sub10761, sub10938]
  rfl
theorem sub10940 (p : Pattern) : d2163 (change p 204 (some 182)) = d6023 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1806 (change p 204 (some 182))) = d6023 p
  rw [sub10415, sub10569]
  rfl
theorem sub10941 (p : Pattern) : d2164 (change p 204 (some 182)) = d6024 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d2163 (change p 204 (some 182))) = d6024 p
  rw [sub10415, sub10940]
  rfl
theorem sub10942 (p : Pattern) : d2165 (change p 204 (some 182)) = d6025 p := by
  change (if p 160 then d2164 (change p 204 (some 182)) else d2162 (change p 204 (some 182))) = d6025 p
  rw [sub10941, sub10939]
  rfl
theorem sub10943 (p : Pattern) : d2166 (change p 204 (some 182)) = d6026 p := by
  change (if p 141 then d2165 (change p 204 (some 182)) else d2153 (change p 204 (some 182))) = d6026 p
  rw [sub10942, sub10930]
  rfl
theorem sub10944 (p : Pattern) : d2167 (change p 204 (some 182)) = d6027 p := by
  change (if p 138 then d2166 (change p 204 (some 182)) else d2148 (change p 204 (some 182))) = d6027 p
  rw [sub10943, sub10925]
  rfl
theorem sub10945 (p : Pattern) : d2168 (change p 204 (some 182)) = d6028 p := by
  change (if p 163 then d1805 (change p 204 (some 182)) else d1973 (change p 204 (some 182))) = d6028 p
  rw [sub10568, sub10748]
  rfl
theorem sub10946 (p : Pattern) : d2169 (change p 204 (some 182)) = d6029 p := by
  change (if p 162 then d2168 (change p 204 (some 182)) else d2149 (change p 204 (some 182))) = d6029 p
  rw [sub10945, sub10926]
  rfl
theorem sub10947 (p : Pattern) : d2170 (change p 204 (some 182)) = d6030 p := by
  change (if p 163 then d1805 (change p 204 (some 182)) else d1968 (change p 204 (some 182))) = d6030 p
  rw [sub10568, sub10743]
  rfl
theorem sub10948 (p : Pattern) : d2171 (change p 204 (some 182)) = d6031 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2170 (change p 204 (some 182))) = d6031 p
  rw [sub10415, sub10947]
  rfl
theorem sub10949 (p : Pattern) : d2172 (change p 204 (some 182)) = d6032 p := by
  change (if p 161 then d2171 (change p 204 (some 182)) else d2169 (change p 204 (some 182))) = d6032 p
  rw [sub10948, sub10946]
  rfl
theorem sub10950 (p : Pattern) : d2173 (change p 204 (some 182)) = d6033 p := by
  change (if p 163 then d1756 (change p 204 (some 182)) else d1974 (change p 204 (some 182))) = d6033 p
  rw [sub10514, sub10749]
  rfl
theorem sub10951 (p : Pattern) : d2174 (change p 204 (some 182)) = d6034 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2173 (change p 204 (some 182))) = d6034 p
  rw [sub10415, sub10950]
  rfl
theorem sub10952 (p : Pattern) : d2175 (change p 204 (some 182)) = d6035 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d2174 (change p 204 (some 182))) = d6035 p
  rw [sub10415, sub10951]
  rfl
theorem sub10953 (p : Pattern) : d2176 (change p 204 (some 182)) = d6036 p := by
  change (if p 160 then d2175 (change p 204 (some 182)) else d2172 (change p 204 (some 182))) = d6036 p
  rw [sub10952, sub10949]
  rfl
theorem sub10954 (p : Pattern) : d2177 (change p 204 (some 182)) = d6037 p := by
  change (if p 141 then d2165 (change p 204 (some 182)) else d2176 (change p 204 (some 182))) = d6037 p
  rw [sub10942, sub10953]
  rfl
theorem sub10955 (p : Pattern) : d2178 (change p 204 (some 182)) = d6038 p := by
  change (if p 138 then d12 (change p 204 (some 182)) else d2177 (change p 204 (some 182))) = d6038 p
  rw [sub10415, sub10954]
  rfl
theorem sub10956 (p : Pattern) : d2179 (change p 204 (some 182)) = d6039 p := by
  change (if p 116 then d2178 (change p 204 (some 182)) else d2167 (change p 204 (some 182))) = d6039 p
  rw [sub10955, sub10944]
  rfl
theorem sub10957 (p : Pattern) : d2180 (change p 204 (some 182)) = d6040 p := by
  change (if p 115 then d2179 (change p 204 (some 182)) else d2106 (change p 204 (some 182))) = d6040 p
  rw [sub10956, sub10883]
  rfl
theorem sub10958 (p : Pattern) : d2181 (change p 204 (some 182)) = d6041 p := by
  change (if p 71 then d2180 (change p 204 (some 182)) else d1849 (change p 204 (some 182))) = d6041 p
  rw [sub10957, sub10612]
  rfl
theorem sub10959 (p : Pattern) : d2182 (change p 204 (some 182)) = d6042 p := by
  change (if p 49 then d2181 (change p 204 (some 182)) else d2087 (change p 204 (some 182))) = d6042 p
  rw [sub10958, sub10864]
  rfl
theorem sub10960 (p : Pattern) : d2183 (change p 204 (some 182)) = d6043 p := by
  change (if p 48 then d2182 (change p 204 (some 182)) else d2010 (change p 204 (some 182))) = d6043 p
  rw [sub10959, sub10785]
  rfl
theorem sub10961 (p : Pattern) : d0 (change p 225 (some 224)) = d0 p := by
  rfl
theorem sub10962 (p : Pattern) : d12 (change p 225 (some 224)) = d12 p := by
  rfl
theorem sub10963 (p : Pattern) : d13 (change p 225 (some 224)) = d13 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d0 (change p 225 (some 224))) = d13 p
  rw [sub10962, sub10961]
  rfl
theorem sub10964 (p : Pattern) : d14 (change p 225 (some 224)) = d14 p := by
  change (if p 246 then d13 (change p 225 (some 224)) else d0 (change p 225 (some 224))) = d14 p
  rw [sub10963, sub10961]
  rfl
theorem sub10965 (p : Pattern) : d2504 (change p 225 (some 224)) = d14 p := by
  change d14 (change p 225 (some 224)) = d14 p
  exact sub10964 p
theorem sub10966 (p : Pattern) : d2505 (change p 225 (some 224)) = d14 p := by
  change d2504 (change p 225 (some 224)) = d14 p
  exact sub10965 p
theorem sub10967 (p : Pattern) : d4 (change p 225 (some 224)) = d4 p := by
  rfl
theorem sub10968 (p : Pattern) : d1769 (change p 225 (some 224)) = d1769 p := by
  change (if p 247 then d4 (change p 225 (some 224)) else d0 (change p 225 (some 224))) = d1769 p
  rw [sub10967, sub10961]
  rfl
theorem sub10969 (p : Pattern) : d17 (change p 225 (some 224)) = d17 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d4 (change p 225 (some 224))) = d17 p
  rw [sub10962, sub10967]
  rfl
theorem sub10970 (p : Pattern) : d1770 (change p 225 (some 224)) = d1770 p := by
  change (if p 246 then d17 (change p 225 (some 224)) else d1769 (change p 225 (some 224))) = d1770 p
  rw [sub10969, sub10968]
  rfl
theorem sub10971 (p : Pattern) : d2506 (change p 225 (some 224)) = d1770 p := by
  change d1770 (change p 225 (some 224)) = d1770 p
  exact sub10970 p
theorem sub10972 (p : Pattern) : d2507 (change p 225 (some 224)) = d1770 p := by
  change d2506 (change p 225 (some 224)) = d1770 p
  exact sub10971 p
theorem sub10973 (p : Pattern) : d2508 (change p 225 (some 224)) = d6044 p := by
  change (if p 204 then d2507 (change p 225 (some 224)) else d2505 (change p 225 (some 224))) = d6044 p
  rw [sub10972, sub10966]
  rfl
theorem sub10974 (p : Pattern) : d2 (change p 225 (some 224)) = d2 p := by
  rfl
theorem sub10975 (p : Pattern) : d1683 (change p 225 (some 224)) = d1683 p := by
  change (if p 247 then d2 (change p 225 (some 224)) else d0 (change p 225 (some 224))) = d1683 p
  rw [sub10974, sub10961]
  rfl
theorem sub10976 (p : Pattern) : d30 (change p 225 (some 224)) = d30 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d2 (change p 225 (some 224))) = d30 p
  rw [sub10962, sub10974]
  rfl
theorem sub10977 (p : Pattern) : d1684 (change p 225 (some 224)) = d1684 p := by
  change (if p 246 then d30 (change p 225 (some 224)) else d1683 (change p 225 (some 224))) = d1684 p
  rw [sub10976, sub10975]
  rfl
theorem sub10978 (p : Pattern) : d2509 (change p 225 (some 224)) = d1684 p := by
  change d1684 (change p 225 (some 224)) = d1684 p
  exact sub10977 p
theorem sub10979 (p : Pattern) : d2510 (change p 225 (some 224)) = d1684 p := by
  change d2509 (change p 225 (some 224)) = d1684 p
  exact sub10978 p
theorem sub10980 (p : Pattern) : d2511 (change p 225 (some 224)) = d6045 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2510 (change p 225 (some 224))) = d6045 p
  rw [sub10962, sub10979]
  rfl
theorem sub10981 (p : Pattern) : d2512 (change p 225 (some 224)) = d6046 p := by
  change (if p 182 then d2511 (change p 225 (some 224)) else d2508 (change p 225 (some 224))) = d6046 p
  rw [sub10980, sub10973]
  rfl
theorem sub10982 (p : Pattern) : d2514 (change p 225 (some 224)) = d14 p := by
  change d2504 (change p 225 (some 224)) = d14 p
  exact sub10965 p
theorem sub10983 (p : Pattern) : d2515 (change p 225 (some 224)) = d6044 p := by
  change (if p 204 then d2507 (change p 225 (some 224)) else d2514 (change p 225 (some 224))) = d6044 p
  rw [sub10972, sub10982]
  rfl
theorem sub10984 (p : Pattern) : d2516 (change p 225 (some 224)) = d6046 p := by
  change (if p 182 then d2511 (change p 225 (some 224)) else d2515 (change p 225 (some 224))) = d6046 p
  rw [sub10980, sub10983]
  rfl
theorem sub10985 (p : Pattern) : d2517 (change p 225 (some 224)) = d6046 p := by
  change (if p 163 then d2516 (change p 225 (some 224)) else d2512 (change p 225 (some 224))) = d6046 p
  rw [sub10984, sub10981]
  simp only [ite_self]
theorem sub10986 (p : Pattern) : d2518 (change p 225 (some 224)) = d6044 p := by
  change (if p 204 then d2507 (change p 225 (some 224)) else d2504 (change p 225 (some 224))) = d6044 p
  rw [sub10972, sub10965]
  rfl
theorem sub10987 (p : Pattern) : d2519 (change p 225 (some 224)) = d6046 p := by
  change (if p 182 then d2511 (change p 225 (some 224)) else d2518 (change p 225 (some 224))) = d6046 p
  rw [sub10980, sub10986]
  rfl
theorem sub10988 (p : Pattern) : d18 (change p 225 (some 224)) = d18 p := by
  change (if p 246 then d17 (change p 225 (some 224)) else d4 (change p 225 (some 224))) = d18 p
  rw [sub10969, sub10967]
  rfl
theorem sub10989 (p : Pattern) : d2520 (change p 225 (some 224)) = d18 p := by
  change d18 (change p 225 (some 224)) = d18 p
  exact sub10988 p
theorem sub10990 (p : Pattern) : d8 (change p 225 (some 224)) = d8 p := by
  rfl
theorem sub10991 (p : Pattern) : d1794 (change p 225 (some 224)) = d1794 p := by
  change (if p 247 then d8 (change p 225 (some 224)) else d4 (change p 225 (some 224))) = d1794 p
  rw [sub10990, sub10967]
  rfl
theorem sub10992 (p : Pattern) : d190 (change p 225 (some 224)) = d190 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d8 (change p 225 (some 224))) = d190 p
  rw [sub10962, sub10990]
  rfl
theorem sub10993 (p : Pattern) : d1795 (change p 225 (some 224)) = d1795 p := by
  change (if p 246 then d190 (change p 225 (some 224)) else d1794 (change p 225 (some 224))) = d1795 p
  rw [sub10992, sub10991]
  rfl
theorem sub10994 (p : Pattern) : d2521 (change p 225 (some 224)) = d1795 p := by
  change d1795 (change p 225 (some 224)) = d1795 p
  exact sub10993 p
theorem sub10995 (p : Pattern) : d2522 (change p 225 (some 224)) = d1795 p := by
  change d2521 (change p 225 (some 224)) = d1795 p
  exact sub10994 p
theorem sub10996 (p : Pattern) : d2523 (change p 225 (some 224)) = d6047 p := by
  change (if p 204 then d2522 (change p 225 (some 224)) else d2520 (change p 225 (some 224))) = d6047 p
  rw [sub10995, sub10989]
  rfl
theorem sub10997 (p : Pattern) : d6 (change p 225 (some 224)) = d6 p := by
  rfl
theorem sub10998 (p : Pattern) : d1693 (change p 225 (some 224)) = d1693 p := by
  change (if p 247 then d6 (change p 225 (some 224)) else d4 (change p 225 (some 224))) = d1693 p
  rw [sub10997, sub10967]
  rfl
theorem sub10999 (p : Pattern) : d34 (change p 225 (some 224)) = d34 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d6 (change p 225 (some 224))) = d34 p
  rw [sub10962, sub10997]
  rfl
theorem sub11000 (p : Pattern) : d1694 (change p 225 (some 224)) = d1694 p := by
  change (if p 246 then d34 (change p 225 (some 224)) else d1693 (change p 225 (some 224))) = d1694 p
  rw [sub10999, sub10998]
  rfl
theorem sub11001 (p : Pattern) : d2524 (change p 225 (some 224)) = d1694 p := by
  change d1694 (change p 225 (some 224)) = d1694 p
  exact sub11000 p
theorem sub11002 (p : Pattern) : d2525 (change p 225 (some 224)) = d1694 p := by
  change d2524 (change p 225 (some 224)) = d1694 p
  exact sub11001 p
theorem sub11003 (p : Pattern) : d2526 (change p 225 (some 224)) = d6048 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2525 (change p 225 (some 224))) = d6048 p
  rw [sub10962, sub11002]
  rfl
theorem sub11004 (p : Pattern) : d2527 (change p 225 (some 224)) = d6049 p := by
  change (if p 182 then d2526 (change p 225 (some 224)) else d2523 (change p 225 (some 224))) = d6049 p
  rw [sub11003, sub10996]
  rfl
theorem sub11005 (p : Pattern) : d2528 (change p 225 (some 224)) = d6050 p := by
  change (if p 163 then d2527 (change p 225 (some 224)) else d2519 (change p 225 (some 224))) = d6050 p
  rw [sub11004, sub10987]
  rfl
theorem sub11006 (p : Pattern) : d2529 (change p 225 (some 224)) = d6051 p := by
  change (if p 162 then d2528 (change p 225 (some 224)) else d2517 (change p 225 (some 224))) = d6051 p
  rw [sub11005, sub10985]
  rfl
theorem sub11007 (p : Pattern) : d9 (change p 225 (some 224)) = d9 p := by
  rfl
theorem sub11008 (p : Pattern) : d23 (change p 225 (some 224)) = d23 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d9 (change p 225 (some 224))) = d23 p
  rw [sub10962, sub11007]
  rfl
theorem sub11009 (p : Pattern) : d24 (change p 225 (some 224)) = d24 p := by
  change (if p 246 then d23 (change p 225 (some 224)) else d9 (change p 225 (some 224))) = d24 p
  rw [sub11008, sub11007]
  rfl
theorem sub11010 (p : Pattern) : d2530 (change p 225 (some 224)) = d24 p := by
  change d24 (change p 225 (some 224)) = d24 p
  exact sub11009 p
theorem sub11011 (p : Pattern) : d356 (change p 225 (some 224)) = d356 p := by
  change (if p 246 then d12 (change p 225 (some 224)) else d23 (change p 225 (some 224))) = d356 p
  rw [sub10962, sub11008]
  rfl
theorem sub11012 (p : Pattern) : d357 (change p 225 (some 224)) = d356 p := by
  change d356 (change p 225 (some 224)) = d356 p
  exact sub11011 p
theorem sub11013 (p : Pattern) : d2531 (change p 225 (some 224)) = d356 p := by
  change d357 (change p 225 (some 224)) = d356 p
  exact sub11012 p
theorem sub11014 (p : Pattern) : d2532 (change p 225 (some 224)) = d6052 p := by
  change (if p 204 then d2531 (change p 225 (some 224)) else d2530 (change p 225 (some 224))) = d6052 p
  rw [sub11013, sub11010]
  rfl
theorem sub11015 (p : Pattern) : d11 (change p 225 (some 224)) = d11 p := by
  rfl
theorem sub11016 (p : Pattern) : d1701 (change p 225 (some 224)) = d1701 p := by
  change (if p 247 then d11 (change p 225 (some 224)) else d9 (change p 225 (some 224))) = d1701 p
  rw [sub11015, sub11007]
  rfl
theorem sub11017 (p : Pattern) : d39 (change p 225 (some 224)) = d39 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d11 (change p 225 (some 224))) = d39 p
  rw [sub10962, sub11015]
  rfl
theorem sub11018 (p : Pattern) : d1702 (change p 225 (some 224)) = d1702 p := by
  change (if p 246 then d39 (change p 225 (some 224)) else d1701 (change p 225 (some 224))) = d1702 p
  rw [sub11017, sub11016]
  rfl
theorem sub11019 (p : Pattern) : d2533 (change p 225 (some 224)) = d1702 p := by
  change d1702 (change p 225 (some 224)) = d1702 p
  exact sub11018 p
theorem sub11020 (p : Pattern) : d2534 (change p 225 (some 224)) = d1702 p := by
  change d2533 (change p 225 (some 224)) = d1702 p
  exact sub11019 p
theorem sub11021 (p : Pattern) : d2535 (change p 225 (some 224)) = d6053 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2534 (change p 225 (some 224))) = d6053 p
  rw [sub10962, sub11020]
  rfl
theorem sub11022 (p : Pattern) : d2536 (change p 225 (some 224)) = d6054 p := by
  change (if p 182 then d2535 (change p 225 (some 224)) else d2532 (change p 225 (some 224))) = d6054 p
  rw [sub11021, sub11014]
  rfl
theorem sub11023 (p : Pattern) : d2537 (change p 225 (some 224)) = d6055 p := by
  change (if p 163 then d12 (change p 225 (some 224)) else d2536 (change p 225 (some 224))) = d6055 p
  rw [sub10962, sub11022]
  rfl
theorem sub11024 (p : Pattern) : d2538 (change p 225 (some 224)) = d6056 p := by
  change (if p 162 then d2537 (change p 225 (some 224)) else d2528 (change p 225 (some 224))) = d6056 p
  rw [sub11023, sub11005]
  rfl
theorem sub11025 (p : Pattern) : d2539 (change p 225 (some 224)) = d6057 p := by
  change (if p 161 then d2538 (change p 225 (some 224)) else d2529 (change p 225 (some 224))) = d6057 p
  rw [sub11024, sub11006]
  rfl
theorem sub11026 (p : Pattern) : d1713 (change p 225 (some 224)) = d1713 p := by
  change (if p 247 then d6 (change p 225 (some 224)) else d2 (change p 225 (some 224))) = d1713 p
  rw [sub10997, sub10974]
  rfl
theorem sub11027 (p : Pattern) : d1714 (change p 225 (some 224)) = d1714 p := by
  change (if p 246 then d34 (change p 225 (some 224)) else d1713 (change p 225 (some 224))) = d1714 p
  rw [sub10999, sub11026]
  rfl
theorem sub11028 (p : Pattern) : d2541 (change p 225 (some 224)) = d1714 p := by
  change d1714 (change p 225 (some 224)) = d1714 p
  exact sub11027 p
theorem sub11029 (p : Pattern) : d2542 (change p 225 (some 224)) = d1714 p := by
  change d2541 (change p 225 (some 224)) = d1714 p
  exact sub11028 p
theorem sub11030 (p : Pattern) : d2543 (change p 225 (some 224)) = d6058 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2542 (change p 225 (some 224))) = d6058 p
  rw [sub10962, sub11029]
  rfl
theorem sub11031 (p : Pattern) : d2544 (change p 225 (some 224)) = d6059 p := by
  change (if p 182 then d2543 (change p 225 (some 224)) else d2518 (change p 225 (some 224))) = d6059 p
  rw [sub11030, sub10986]
  rfl
theorem sub11032 (p : Pattern) : d10 (change p 225 (some 224)) = d10 p := by
  rfl
theorem sub11033 (p : Pattern) : d1721 (change p 225 (some 224)) = d1721 p := by
  change (if p 247 then d10 (change p 225 (some 224)) else d6 (change p 225 (some 224))) = d1721 p
  rw [sub11032, sub10997]
  rfl
theorem sub11034 (p : Pattern) : d57 (change p 225 (some 224)) = d57 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d10 (change p 225 (some 224))) = d57 p
  rw [sub10962, sub11032]
  rfl
theorem sub11035 (p : Pattern) : d1722 (change p 225 (some 224)) = d1722 p := by
  change (if p 246 then d57 (change p 225 (some 224)) else d1721 (change p 225 (some 224))) = d1722 p
  rw [sub11034, sub11033]
  rfl
theorem sub11036 (p : Pattern) : d2546 (change p 225 (some 224)) = d1722 p := by
  change d1722 (change p 225 (some 224)) = d1722 p
  exact sub11035 p
theorem sub11037 (p : Pattern) : d2547 (change p 225 (some 224)) = d1722 p := by
  change d2546 (change p 225 (some 224)) = d1722 p
  exact sub11036 p
theorem sub11038 (p : Pattern) : d2548 (change p 225 (some 224)) = d6060 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2547 (change p 225 (some 224))) = d6060 p
  rw [sub10962, sub11037]
  rfl
theorem sub11039 (p : Pattern) : d2549 (change p 225 (some 224)) = d6061 p := by
  change (if p 182 then d2548 (change p 225 (some 224)) else d2518 (change p 225 (some 224))) = d6061 p
  rw [sub11038, sub10986]
  rfl
end NetHack.Sokoban22Refined85
