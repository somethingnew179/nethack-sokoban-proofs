/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2160 (p : Pattern) : d9 (change p 10000 (some 134)) = d9 p := by
  change (if p 161 then d2 (change p 10000 (some 134)) else d1 (change p 10000 (some 134))) = d9 p
  rw [sub2152, sub2159]
  rfl
theorem sub2161 (p : Pattern) : d10 (change p 10000 (some 134)) = d10 p := by
  change (if p 160 then d9 (change p 10000 (some 134)) else d1 (change p 10000 (some 134))) = d10 p
  rw [sub2160, sub2159]
  rfl
theorem sub2162 (p : Pattern) : d11 (change p 10000 (some 134)) = d11 p := by
  change (if p 160 then d2 (change p 10000 (some 134)) else d1 (change p 10000 (some 134))) = d11 p
  rw [sub2152, sub2159]
  rfl
theorem sub2163 (p : Pattern) : d12 (change p 10000 (some 134)) = d12 p := by
  change (if p 159 then d11 (change p 10000 (some 134)) else d10 (change p 10000 (some 134))) = d12 p
  rw [sub2162, sub2161]
  rfl
theorem sub2164 (p : Pattern) : d13 (change p 10000 (some 134)) = d13 p := by
  change (if p 159 then d2 (change p 10000 (some 134)) else d10 (change p 10000 (some 134))) = d13 p
  rw [sub2152, sub2161]
  rfl
theorem sub2165 (p : Pattern) : d14 (change p 10000 (some 134)) = d14 p := by
  change (if p 158 then d13 (change p 10000 (some 134)) else d12 (change p 10000 (some 134))) = d14 p
  rw [sub2164, sub2163]
  rfl
theorem sub2166 (p : Pattern) : d15 (change p 10000 (some 134)) = d15 p := by
  change (if p 139 then d14 (change p 10000 (some 134)) else d8 (change p 10000 (some 134))) = d15 p
  rw [sub2165, sub2158]
  rfl
theorem sub2167 (p : Pattern) : d16 (change p 10000 (some 134)) = d16 p := by
  change (if p 138 then d15 (change p 10000 (some 134)) else d8 (change p 10000 (some 134))) = d16 p
  rw [sub2166, sub2158]
  rfl
theorem sub2168 (p : Pattern) : d17 (change p 10000 (some 134)) = d17 p := by
  change (if p 160 then d2 (change p 10000 (some 134)) else d3 (change p 10000 (some 134))) = d17 p
  rw [sub2152, sub2153]
  rfl
theorem sub2169 (p : Pattern) : d18 (change p 10000 (some 134)) = d18 p := by
  change (if p 159 then d17 (change p 10000 (some 134)) else d4 (change p 10000 (some 134))) = d18 p
  rw [sub2168, sub2154]
  rfl
theorem sub2170 (p : Pattern) : d19 (change p 10000 (some 134)) = d19 p := by
  change (if p 159 then d2 (change p 10000 (some 134)) else d17 (change p 10000 (some 134))) = d19 p
  rw [sub2152, sub2168]
  rfl
theorem sub2171 (p : Pattern) : d20 (change p 10000 (some 134)) = d20 p := by
  change (if p 158 then d19 (change p 10000 (some 134)) else d18 (change p 10000 (some 134))) = d20 p
  rw [sub2170, sub2169]
  rfl
theorem sub2172 (p : Pattern) : d21 (change p 10000 (some 134)) = d21 p := by
  change (if p 160 then d2 (change p 10000 (some 134)) else d9 (change p 10000 (some 134))) = d21 p
  rw [sub2152, sub2160]
  rfl
theorem sub2173 (p : Pattern) : d22 (change p 10000 (some 134)) = d22 p := by
  change (if p 159 then d21 (change p 10000 (some 134)) else d10 (change p 10000 (some 134))) = d22 p
  rw [sub2172, sub2161]
  rfl
theorem sub2174 (p : Pattern) : d23 (change p 10000 (some 134)) = d23 p := by
  change (if p 159 then d2 (change p 10000 (some 134)) else d21 (change p 10000 (some 134))) = d23 p
  rw [sub2152, sub2172]
  rfl
theorem sub2175 (p : Pattern) : d24 (change p 10000 (some 134)) = d24 p := by
  change (if p 158 then d23 (change p 10000 (some 134)) else d22 (change p 10000 (some 134))) = d24 p
  rw [sub2174, sub2173]
  rfl
theorem sub2176 (p : Pattern) : d25 (change p 10000 (some 134)) = d25 p := by
  change (if p 139 then d24 (change p 10000 (some 134)) else d20 (change p 10000 (some 134))) = d25 p
  rw [sub2175, sub2171]
  rfl
theorem sub2177 (p : Pattern) : d26 (change p 10000 (some 134)) = d26 p := by
  change (if p 138 then d25 (change p 10000 (some 134)) else d20 (change p 10000 (some 134))) = d26 p
  rw [sub2176, sub2171]
  rfl
theorem sub2178 (p : Pattern) : d27 (change p 10000 (some 134)) = d26 p := by
  change d26 (change p 10000 (some 134)) = d26 p
  exact sub2177 p
theorem sub2179 (p : Pattern) : d28 (change p 10000 (some 134)) = d1309 p := by
  change (if p 133 then d27 (change p 10000 (some 134)) else d16 (change p 10000 (some 134))) = d1309 p
  rw [sub2178, sub2167]
  rfl
theorem sub2180 (p : Pattern) : d29 (change p 10000 (some 134)) = d29 p := by
  change (if p 161 then d1 (change p 10000 (some 134)) else d0 (change p 10000 (some 134))) = d29 p
  rw [sub2159, sub2151]
  rfl
theorem sub2181 (p : Pattern) : d30 (change p 10000 (some 134)) = d30 p := by
  change (if p 160 then d2 (change p 10000 (some 134)) else d29 (change p 10000 (some 134))) = d30 p
  rw [sub2152, sub2180]
  rfl
theorem sub2182 (p : Pattern) : d31 (change p 10000 (some 134)) = d31 p := by
  change (if p 159 then d30 (change p 10000 (some 134)) else d4 (change p 10000 (some 134))) = d31 p
  rw [sub2181, sub2154]
  rfl
theorem sub2183 (p : Pattern) : d32 (change p 10000 (some 134)) = d32 p := by
  change (if p 159 then d2 (change p 10000 (some 134)) else d30 (change p 10000 (some 134))) = d32 p
  rw [sub2152, sub2181]
  rfl
theorem sub2184 (p : Pattern) : d33 (change p 10000 (some 134)) = d33 p := by
  change (if p 158 then d32 (change p 10000 (some 134)) else d31 (change p 10000 (some 134))) = d33 p
  rw [sub2183, sub2182]
  rfl
theorem sub2185 (p : Pattern) : d34 (change p 10000 (some 134)) = d34 p := by
  change (if p 139 then d24 (change p 10000 (some 134)) else d33 (change p 10000 (some 134))) = d34 p
  rw [sub2175, sub2184]
  rfl
theorem sub2186 (p : Pattern) : d35 (change p 10000 (some 134)) = d35 p := by
  change (if p 138 then d34 (change p 10000 (some 134)) else d33 (change p 10000 (some 134))) = d35 p
  rw [sub2185, sub2184]
  rfl
theorem sub2187 (p : Pattern) : d36 (change p 10000 (some 134)) = d35 p := by
  change d35 (change p 10000 (some 134)) = d35 p
  exact sub2186 p
theorem sub2188 (p : Pattern) : d43 (change p 10000 (some 134)) = d26 p := by
  change d26 (change p 10000 (some 134)) = d26 p
  exact sub2177 p
theorem sub2189 (p : Pattern) : d44 (change p 10000 (some 134)) = d1310 p := by
  change (if p 133 then d43 (change p 10000 (some 134)) else d36 (change p 10000 (some 134))) = d1310 p
  rw [sub2188, sub2187]
  rfl
theorem sub2190 (p : Pattern) : d45 (change p 10000 (some 134)) = d1311 p := by
  change (if p 132 then d44 (change p 10000 (some 134)) else d28 (change p 10000 (some 134))) = d1311 p
  rw [sub2189, sub2179]
  rfl
theorem sub2191 (p : Pattern) : d46 (change p 10000 (some 134)) = d25 p := by
  change d25 (change p 10000 (some 134)) = d25 p
  exact sub2176 p
theorem sub2192 (p : Pattern) : d47 (change p 10000 (some 134)) = d1312 p := by
  change (if p 133 then d46 (change p 10000 (some 134)) else d15 (change p 10000 (some 134))) = d1312 p
  rw [sub2191, sub2166]
  rfl
theorem sub2193 (p : Pattern) : d48 (change p 10000 (some 134)) = d34 p := by
  change d34 (change p 10000 (some 134)) = d34 p
  exact sub2185 p
theorem sub2194 (p : Pattern) : d49 (change p 10000 (some 134)) = d25 p := by
  change d25 (change p 10000 (some 134)) = d25 p
  exact sub2176 p
theorem sub2195 (p : Pattern) : d50 (change p 10000 (some 134)) = d1313 p := by
  change (if p 133 then d49 (change p 10000 (some 134)) else d48 (change p 10000 (some 134))) = d1313 p
  rw [sub2194, sub2193]
  rfl
theorem sub2196 (p : Pattern) : d51 (change p 10000 (some 134)) = d1314 p := by
  change (if p 132 then d50 (change p 10000 (some 134)) else d47 (change p 10000 (some 134))) = d1314 p
  rw [sub2195, sub2192]
  rfl
theorem sub2197 (p : Pattern) : d52 (change p 10000 (some 134)) = d52 p := by
  change (if p 139 then d2 (change p 10000 (some 134)) else d8 (change p 10000 (some 134))) = d52 p
  rw [sub2152, sub2158]
  rfl
theorem sub2198 (p : Pattern) : d53 (change p 10000 (some 134)) = d53 p := by
  change (if p 138 then d52 (change p 10000 (some 134)) else d15 (change p 10000 (some 134))) = d53 p
  rw [sub2197, sub2166]
  rfl
theorem sub2199 (p : Pattern) : d54 (change p 10000 (some 134)) = d54 p := by
  change (if p 139 then d2 (change p 10000 (some 134)) else d20 (change p 10000 (some 134))) = d54 p
  rw [sub2152, sub2171]
  rfl
theorem sub2200 (p : Pattern) : d55 (change p 10000 (some 134)) = d55 p := by
  change (if p 138 then d54 (change p 10000 (some 134)) else d25 (change p 10000 (some 134))) = d55 p
  rw [sub2199, sub2176]
  rfl
theorem sub2201 (p : Pattern) : d56 (change p 10000 (some 134)) = d55 p := by
  change d55 (change p 10000 (some 134)) = d55 p
  exact sub2200 p
theorem sub2202 (p : Pattern) : d57 (change p 10000 (some 134)) = d1315 p := by
  change (if p 133 then d56 (change p 10000 (some 134)) else d53 (change p 10000 (some 134))) = d1315 p
  rw [sub2201, sub2198]
  rfl
theorem sub2203 (p : Pattern) : d58 (change p 10000 (some 134)) = d58 p := by
  change (if p 139 then d2 (change p 10000 (some 134)) else d33 (change p 10000 (some 134))) = d58 p
  rw [sub2152, sub2184]
  rfl
theorem sub2204 (p : Pattern) : d59 (change p 10000 (some 134)) = d59 p := by
  change (if p 138 then d58 (change p 10000 (some 134)) else d34 (change p 10000 (some 134))) = d59 p
  rw [sub2203, sub2185]
  rfl
theorem sub2205 (p : Pattern) : d60 (change p 10000 (some 134)) = d59 p := by
  change d59 (change p 10000 (some 134)) = d59 p
  exact sub2204 p
theorem sub2206 (p : Pattern) : d63 (change p 10000 (some 134)) = d55 p := by
  change d55 (change p 10000 (some 134)) = d55 p
  exact sub2200 p
theorem sub2207 (p : Pattern) : d64 (change p 10000 (some 134)) = d1316 p := by
  change (if p 133 then d63 (change p 10000 (some 134)) else d60 (change p 10000 (some 134))) = d1316 p
  rw [sub2206, sub2205]
  rfl
theorem sub2208 (p : Pattern) : d65 (change p 10000 (some 134)) = d1317 p := by
  change (if p 132 then d64 (change p 10000 (some 134)) else d57 (change p 10000 (some 134))) = d1317 p
  rw [sub2207, sub2202]
  rfl
theorem sub2209 (p : Pattern) : d66 (change p 10000 (some 134)) = d1318 p := by
  change (if p 113 then d65 (change p 10000 (some 134)) else d51 (change p 10000 (some 134))) = d1318 p
  rw [sub2208, sub2196]
  rfl
theorem sub2210 (p : Pattern) : d67 (change p 10000 (some 134)) = d1319 p := by
  change (if p 112 then d66 (change p 10000 (some 134)) else d45 (change p 10000 (some 134))) = d1319 p
  rw [sub2209, sub2190]
  rfl
theorem sub2211 (p : Pattern) : d70 (change p 10000 (some 134)) = d70 p := by
  change (if p 139 then d2 (change p 10000 (some 134)) else d24 (change p 10000 (some 134))) = d70 p
  rw [sub2152, sub2175]
  rfl
theorem sub2212 (p : Pattern) : d71 (change p 10000 (some 134)) = d71 p := by
  change (if p 138 then d70 (change p 10000 (some 134)) else d24 (change p 10000 (some 134))) = d71 p
  rw [sub2211, sub2175]
  rfl
theorem sub2213 (p : Pattern) : d72 (change p 10000 (some 134)) = d71 p := by
  change d71 (change p 10000 (some 134)) = d71 p
  exact sub2212 p
theorem sub2214 (p : Pattern) : d73 (change p 10000 (some 134)) = d1320 p := by
  change (if p 133 then d72 (change p 10000 (some 134)) else d27 (change p 10000 (some 134))) = d1320 p
  rw [sub2213, sub2178]
  rfl
theorem sub2215 (p : Pattern) : d74 (change p 10000 (some 134)) = d1321 p := by
  change (if p 132 then d73 (change p 10000 (some 134)) else d28 (change p 10000 (some 134))) = d1321 p
  rw [sub2214, sub2179]
  rfl
theorem sub2216 (p : Pattern) : d75 (change p 10000 (some 134)) = d70 p := by
  change d70 (change p 10000 (some 134)) = d70 p
  exact sub2211 p
theorem sub2217 (p : Pattern) : d76 (change p 10000 (some 134)) = d1322 p := by
  change (if p 133 then d75 (change p 10000 (some 134)) else d27 (change p 10000 (some 134))) = d1322 p
  rw [sub2216, sub2178]
  rfl
theorem sub2218 (p : Pattern) : d77 (change p 10000 (some 134)) = d1323 p := by
  change (if p 132 then d76 (change p 10000 (some 134)) else d28 (change p 10000 (some 134))) = d1323 p
  rw [sub2217, sub2179]
  rfl
theorem sub2219 (p : Pattern) : d78 (change p 10000 (some 134)) = d1324 p := by
  change (if p 113 then d77 (change p 10000 (some 134)) else d74 (change p 10000 (some 134))) = d1324 p
  rw [sub2218, sub2215]
  rfl
theorem sub2220 (p : Pattern) : d79 (change p 10000 (some 134)) = d1325 p := by
  change (if p 133 then d75 (change p 10000 (some 134)) else d46 (change p 10000 (some 134))) = d1325 p
  rw [sub2216, sub2191]
  rfl
theorem sub2221 (p : Pattern) : d80 (change p 10000 (some 134)) = d1326 p := by
  change (if p 132 then d79 (change p 10000 (some 134)) else d47 (change p 10000 (some 134))) = d1326 p
  rw [sub2220, sub2192]
  rfl
theorem sub2222 (p : Pattern) : d81 (change p 10000 (some 134)) = d1327 p := by
  change (if p 133 then d75 (change p 10000 (some 134)) else d56 (change p 10000 (some 134))) = d1327 p
  rw [sub2216, sub2201]
  rfl
theorem sub2223 (p : Pattern) : d82 (change p 10000 (some 134)) = d1328 p := by
  change (if p 132 then d81 (change p 10000 (some 134)) else d57 (change p 10000 (some 134))) = d1328 p
  rw [sub2222, sub2202]
  rfl
theorem sub2224 (p : Pattern) : d83 (change p 10000 (some 134)) = d1329 p := by
  change (if p 113 then d82 (change p 10000 (some 134)) else d80 (change p 10000 (some 134))) = d1329 p
  rw [sub2223, sub2221]
  rfl
theorem sub2225 (p : Pattern) : d84 (change p 10000 (some 134)) = d1330 p := by
  change (if p 112 then d83 (change p 10000 (some 134)) else d78 (change p 10000 (some 134))) = d1330 p
  rw [sub2224, sub2219]
  rfl
theorem sub2226 (p : Pattern) : d85 (change p 10000 (some 134)) = d1331 p := by
  change (if p 106 then d84 (change p 10000 (some 134)) else d67 (change p 10000 (some 134))) = d1331 p
  rw [sub2225, sub2210]
  rfl
theorem sub2227 (p : Pattern) : d86 (change p 10000 (some 134)) = d86 p := by
  change (if p 138 then d52 (change p 10000 (some 134)) else d8 (change p 10000 (some 134))) = d86 p
  rw [sub2197, sub2158]
  rfl
theorem sub2228 (p : Pattern) : d87 (change p 10000 (some 134)) = d87 p := by
  change (if p 138 then d54 (change p 10000 (some 134)) else d20 (change p 10000 (some 134))) = d87 p
  rw [sub2199, sub2171]
  rfl
theorem sub2229 (p : Pattern) : d88 (change p 10000 (some 134)) = d87 p := by
  change d87 (change p 10000 (some 134)) = d87 p
  exact sub2228 p
theorem sub2230 (p : Pattern) : d89 (change p 10000 (some 134)) = d1332 p := by
  change (if p 133 then d88 (change p 10000 (some 134)) else d86 (change p 10000 (some 134))) = d1332 p
  rw [sub2229, sub2227]
  rfl
theorem sub2231 (p : Pattern) : d90 (change p 10000 (some 134)) = d90 p := by
  change (if p 138 then d58 (change p 10000 (some 134)) else d33 (change p 10000 (some 134))) = d90 p
  rw [sub2203, sub2184]
  rfl
theorem sub2232 (p : Pattern) : d91 (change p 10000 (some 134)) = d90 p := by
  change d90 (change p 10000 (some 134)) = d90 p
  exact sub2231 p
theorem sub2233 (p : Pattern) : d93 (change p 10000 (some 134)) = d87 p := by
  change d87 (change p 10000 (some 134)) = d87 p
  exact sub2228 p
theorem sub2234 (p : Pattern) : d94 (change p 10000 (some 134)) = d1333 p := by
  change (if p 133 then d93 (change p 10000 (some 134)) else d91 (change p 10000 (some 134))) = d1333 p
  rw [sub2233, sub2232]
  rfl
theorem sub2235 (p : Pattern) : d95 (change p 10000 (some 134)) = d1334 p := by
  change (if p 132 then d94 (change p 10000 (some 134)) else d89 (change p 10000 (some 134))) = d1334 p
  rw [sub2234, sub2230]
  rfl
theorem sub2236 (p : Pattern) : d96 (change p 10000 (some 134)) = d1335 p := by
  change (if p 113 then d95 (change p 10000 (some 134)) else d45 (change p 10000 (some 134))) = d1335 p
  rw [sub2235, sub2190]
  rfl
theorem sub2237 (p : Pattern) : d97 (change p 10000 (some 134)) = d97 p := by
  change (if p 139 then d2 (change p 10000 (some 134)) else d14 (change p 10000 (some 134))) = d97 p
  rw [sub2152, sub2165]
  rfl
theorem sub2238 (p : Pattern) : d98 (change p 10000 (some 134)) = d98 p := by
  change (if p 138 then d97 (change p 10000 (some 134)) else d14 (change p 10000 (some 134))) = d98 p
  rw [sub2237, sub2165]
  rfl
theorem sub2239 (p : Pattern) : d99 (change p 10000 (some 134)) = d71 p := by
  change d71 (change p 10000 (some 134)) = d71 p
  exact sub2212 p
theorem sub2240 (p : Pattern) : d100 (change p 10000 (some 134)) = d1336 p := by
  change (if p 133 then d99 (change p 10000 (some 134)) else d98 (change p 10000 (some 134))) = d1336 p
  rw [sub2239, sub2238]
  rfl
theorem sub2241 (p : Pattern) : d101 (change p 10000 (some 134)) = d71 p := by
  change (if p 133 then d72 (change p 10000 (some 134)) else d99 (change p 10000 (some 134))) = d71 p
  rw [sub2213, sub2239]
  simp only [ite_self]
theorem sub2242 (p : Pattern) : d102 (change p 10000 (some 134)) = d1337 p := by
  change (if p 132 then d101 (change p 10000 (some 134)) else d100 (change p 10000 (some 134))) = d1337 p
  rw [sub2241, sub2240]
  rfl
theorem sub2243 (p : Pattern) : d103 (change p 10000 (some 134)) = d1338 p := by
  change (if p 112 then d102 (change p 10000 (some 134)) else d96 (change p 10000 (some 134))) = d1338 p
  rw [sub2242, sub2236]
  rfl
theorem sub2244 (p : Pattern) : d104 (change p 10000 (some 134)) = d1339 p := by
  change (if p 133 then d75 (change p 10000 (some 134)) else d88 (change p 10000 (some 134))) = d1339 p
  rw [sub2216, sub2229]
  rfl
theorem sub2245 (p : Pattern) : d105 (change p 10000 (some 134)) = d1340 p := by
  change (if p 132 then d104 (change p 10000 (some 134)) else d89 (change p 10000 (some 134))) = d1340 p
  rw [sub2244, sub2230]
  rfl
theorem sub2246 (p : Pattern) : d106 (change p 10000 (some 134)) = d1341 p := by
  change (if p 113 then d105 (change p 10000 (some 134)) else d77 (change p 10000 (some 134))) = d1341 p
  rw [sub2245, sub2218]
  rfl
theorem sub2247 (p : Pattern) : d107 (change p 10000 (some 134)) = d1342 p := by
  change (if p 133 then d2 (change p 10000 (some 134)) else d99 (change p 10000 (some 134))) = d1342 p
  rw [sub2152, sub2239]
  rfl
theorem sub2248 (p : Pattern) : d108 (change p 10000 (some 134)) = d1343 p := by
  change (if p 132 then d107 (change p 10000 (some 134)) else d100 (change p 10000 (some 134))) = d1343 p
  rw [sub2247, sub2240]
  rfl
theorem sub2249 (p : Pattern) : d109 (change p 10000 (some 134)) = d70 p := by
  change d70 (change p 10000 (some 134)) = d70 p
  exact sub2211 p
theorem sub2250 (p : Pattern) : d110 (change p 10000 (some 134)) = d1344 p := by
  change (if p 133 then d109 (change p 10000 (some 134)) else d97 (change p 10000 (some 134))) = d1344 p
  rw [sub2249, sub2237]
  rfl
theorem sub2251 (p : Pattern) : d111 (change p 10000 (some 134)) = d1345 p := by
  change (if p 133 then d2 (change p 10000 (some 134)) else d109 (change p 10000 (some 134))) = d1345 p
  rw [sub2152, sub2249]
  rfl
theorem sub2252 (p : Pattern) : d112 (change p 10000 (some 134)) = d1346 p := by
  change (if p 132 then d111 (change p 10000 (some 134)) else d110 (change p 10000 (some 134))) = d1346 p
  rw [sub2251, sub2250]
  rfl
theorem sub2253 (p : Pattern) : d113 (change p 10000 (some 134)) = d1347 p := by
  change (if p 113 then d112 (change p 10000 (some 134)) else d108 (change p 10000 (some 134))) = d1347 p
  rw [sub2252, sub2248]
  rfl
theorem sub2254 (p : Pattern) : d114 (change p 10000 (some 134)) = d1348 p := by
  change (if p 112 then d113 (change p 10000 (some 134)) else d106 (change p 10000 (some 134))) = d1348 p
  rw [sub2253, sub2246]
  rfl
theorem sub2255 (p : Pattern) : d115 (change p 10000 (some 134)) = d1349 p := by
  change (if p 106 then d114 (change p 10000 (some 134)) else d103 (change p 10000 (some 134))) = d1349 p
  rw [sub2254, sub2243]
  rfl
theorem sub2256 (p : Pattern) : d116 (change p 10000 (some 134)) = d1350 p := by
  change (if p 86 then d115 (change p 10000 (some 134)) else d85 (change p 10000 (some 134))) = d1350 p
  rw [sub2255, sub2226]
  rfl
theorem sub2257 (p : Pattern) : d117 (change p 10000 (some 134)) = d1351 p := by
  change (if p 112 then d83 (change p 10000 (some 134)) else d77 (change p 10000 (some 134))) = d1351 p
  rw [sub2224, sub2218]
  rfl
theorem sub2258 (p : Pattern) : d118 (change p 10000 (some 134)) = d1352 p := by
  change (if p 106 then d117 (change p 10000 (some 134)) else d67 (change p 10000 (some 134))) = d1352 p
  rw [sub2257, sub2210]
  rfl
theorem sub2259 (p : Pattern) : d119 (change p 10000 (some 134)) = d119 p := by
  change (if p 139 then d20 (change p 10000 (some 134)) else d33 (change p 10000 (some 134))) = d119 p
  rw [sub2171, sub2184]
  rfl
theorem sub2260 (p : Pattern) : d120 (change p 10000 (some 134)) = d120 p := by
  change (if p 138 then d58 (change p 10000 (some 134)) else d119 (change p 10000 (some 134))) = d120 p
  rw [sub2203, sub2259]
  rfl
theorem sub2261 (p : Pattern) : d121 (change p 10000 (some 134)) = d120 p := by
  change d120 (change p 10000 (some 134)) = d120 p
  exact sub2260 p
theorem sub2262 (p : Pattern) : d122 (change p 10000 (some 134)) = d1353 p := by
  change (if p 133 then d93 (change p 10000 (some 134)) else d121 (change p 10000 (some 134))) = d1353 p
  rw [sub2233, sub2261]
  rfl
theorem sub2263 (p : Pattern) : d123 (change p 10000 (some 134)) = d1354 p := by
  change (if p 132 then d122 (change p 10000 (some 134)) else d89 (change p 10000 (some 134))) = d1354 p
  rw [sub2262, sub2230]
  rfl
theorem sub2264 (p : Pattern) : d124 (change p 10000 (some 134)) = d1355 p := by
  change (if p 113 then d123 (change p 10000 (some 134)) else d45 (change p 10000 (some 134))) = d1355 p
  rw [sub2263, sub2190]
  rfl
theorem sub2265 (p : Pattern) : d125 (change p 10000 (some 134)) = d70 p := by
  change (if p 133 then d75 (change p 10000 (some 134)) else d109 (change p 10000 (some 134))) = d70 p
  rw [sub2216, sub2249]
  simp only [ite_self]
theorem sub2266 (p : Pattern) : d126 (change p 10000 (some 134)) = d1356 p := by
  change (if p 132 then d125 (change p 10000 (some 134)) else d110 (change p 10000 (some 134))) = d1356 p
  rw [sub2265, sub2250]
  rfl
theorem sub2267 (p : Pattern) : d127 (change p 10000 (some 134)) = d1357 p := by
  change (if p 113 then d126 (change p 10000 (some 134)) else d102 (change p 10000 (some 134))) = d1357 p
  rw [sub2266, sub2242]
  rfl
theorem sub2268 (p : Pattern) : d128 (change p 10000 (some 134)) = d1358 p := by
  change (if p 112 then d127 (change p 10000 (some 134)) else d124 (change p 10000 (some 134))) = d1358 p
  rw [sub2267, sub2264]
  rfl
theorem sub2269 (p : Pattern) : d129 (change p 10000 (some 134)) = d1359 p := by
  change (if p 113 then d82 (change p 10000 (some 134)) else d77 (change p 10000 (some 134))) = d1359 p
  rw [sub2223, sub2218]
  rfl
theorem sub2270 (p : Pattern) : d130 (change p 10000 (some 134)) = d1360 p := by
  change (if p 113 then d2 (change p 10000 (some 134)) else d112 (change p 10000 (some 134))) = d1360 p
  rw [sub2152, sub2252]
  rfl
theorem sub2271 (p : Pattern) : d131 (change p 10000 (some 134)) = d1361 p := by
  change (if p 112 then d130 (change p 10000 (some 134)) else d129 (change p 10000 (some 134))) = d1361 p
  rw [sub2270, sub2269]
  rfl
theorem sub2272 (p : Pattern) : d132 (change p 10000 (some 134)) = d1362 p := by
  change (if p 106 then d131 (change p 10000 (some 134)) else d128 (change p 10000 (some 134))) = d1362 p
  rw [sub2271, sub2268]
  rfl
theorem sub2273 (p : Pattern) : d133 (change p 10000 (some 134)) = d1363 p := by
  change (if p 86 then d132 (change p 10000 (some 134)) else d118 (change p 10000 (some 134))) = d1363 p
  rw [sub2272, sub2258]
  rfl
theorem sub2274 (p : Pattern) : d134 (change p 10000 (some 134)) = d1364 p := by
  change (if p 80 then d133 (change p 10000 (some 134)) else d116 (change p 10000 (some 134))) = d1364 p
  rw [sub2273, sub2256]
  rfl
theorem sub2275 (p : Pattern) : d0 (change p 138 (some 139)) = d0 p := by
  rfl
theorem sub2276 (p : Pattern) : d2 (change p 138 (some 139)) = d2 p := by
  rfl
theorem sub2277 (p : Pattern) : d3 (change p 138 (some 139)) = d3 p := by
  change (if p 161 then d2 (change p 138 (some 139)) else d0 (change p 138 (some 139))) = d3 p
  rw [sub2276, sub2275]
  rfl
theorem sub2278 (p : Pattern) : d4 (change p 138 (some 139)) = d4 p := by
  change (if p 160 then d3 (change p 138 (some 139)) else d0 (change p 138 (some 139))) = d4 p
  rw [sub2277, sub2275]
  rfl
theorem sub2279 (p : Pattern) : d5 (change p 138 (some 139)) = d5 p := by
  change (if p 160 then d2 (change p 138 (some 139)) else d0 (change p 138 (some 139))) = d5 p
  rw [sub2276, sub2275]
  rfl
end NetHack.Sokoban32Refined
