/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions67
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub8160 (p : Pattern) : d1376 (change p 163 (some 141)) = d4373 p := by
  change (if p 162 then d1375 (change p 163 (some 141)) else d1289 (change p 163 (some 141))) = d4373 p
  rw [sub8159, sub8087]
  rfl
theorem sub8161 (p : Pattern) : d1377 (change p 163 (some 141)) = d4374 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d1375 (change p 163 (some 141))) = d4374 p
  rw [sub7979, sub8159]
  rfl
theorem sub8162 (p : Pattern) : d1378 (change p 163 (some 141)) = d4375 p := by
  change (if p 161 then d1377 (change p 163 (some 141)) else d1376 (change p 163 (some 141))) = d4375 p
  rw [sub8161, sub8160]
  rfl
theorem sub8163 (p : Pattern) : d1379 (change p 163 (some 141)) = d4376 p := by
  change (if p 160 then d1378 (change p 163 (some 141)) else d1333 (change p 163 (some 141))) = d4376 p
  rw [sub8162, sub8118]
  rfl
theorem sub8164 (p : Pattern) : d1380 (change p 163 (some 141)) = d4376 p := by
  change d1379 (change p 163 (some 141)) = d4376 p
  exact sub8163 p
theorem sub8165 (p : Pattern) : d108 (change p 163 (some 141)) = d108 p := by
  change (if p 204 then d12 (change p 163 (some 141)) else d107 (change p 163 (some 141))) = d108 p
  rw [sub7979, sub8156]
  rfl
theorem sub8166 (p : Pattern) : d298 (change p 163 (some 141)) = d298 p := by
  change (if p 182 then d108 (change p 163 (some 141)) else d282 (change p 163 (some 141))) = d298 p
  rw [sub8165, sub8157]
  rfl
theorem sub8167 (p : Pattern) : d1385 (change p 163 (some 141)) = d298 p := by
  change d298 (change p 163 (some 141)) = d298 p
  exact sub8166 p
theorem sub8168 (p : Pattern) : d1386 (change p 163 (some 141)) = d4382 p := by
  change (if p 162 then d1385 (change p 163 (some 141)) else d1289 (change p 163 (some 141))) = d4382 p
  rw [sub8167, sub8087]
  rfl
theorem sub8169 (p : Pattern) : d1387 (change p 163 (some 141)) = d4383 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d1385 (change p 163 (some 141))) = d4383 p
  rw [sub7979, sub8167]
  rfl
theorem sub8170 (p : Pattern) : d1388 (change p 163 (some 141)) = d4384 p := by
  change (if p 161 then d1387 (change p 163 (some 141)) else d1386 (change p 163 (some 141))) = d4384 p
  rw [sub8169, sub8168]
  rfl
theorem sub8171 (p : Pattern) : d109 (change p 163 (some 141)) = d109 p := by
  change (if p 182 then d108 (change p 163 (some 141)) else d107 (change p 163 (some 141))) = d109 p
  rw [sub8165, sub8156]
  rfl
theorem sub8172 (p : Pattern) : d211 (change p 163 (some 141)) = d109 p := by
  change d109 (change p 163 (some 141)) = d109 p
  exact sub8171 p
theorem sub8173 (p : Pattern) : d213 (change p 163 (some 141)) = d1140 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d211 (change p 163 (some 141))) = d1140 p
  rw [sub7979, sub8172]
  rfl
theorem sub8174 (p : Pattern) : d1389 (change p 163 (some 141)) = d1141 p := by
  change (if p 161 then d12 (change p 163 (some 141)) else d213 (change p 163 (some 141))) = d1141 p
  rw [sub7979, sub8173]
  rfl
theorem sub8175 (p : Pattern) : d1390 (change p 163 (some 141)) = d4385 p := by
  change (if p 160 then d1389 (change p 163 (some 141)) else d1388 (change p 163 (some 141))) = d4385 p
  rw [sub8174, sub8170]
  rfl
theorem sub8176 (p : Pattern) : d1391 (change p 163 (some 141)) = d4385 p := by
  change d1390 (change p 163 (some 141)) = d4385 p
  exact sub8175 p
theorem sub8177 (p : Pattern) : d1392 (change p 163 (some 141)) = d5260 p := by
  change (if p 138 then d1391 (change p 163 (some 141)) else d1380 (change p 163 (some 141))) = d5260 p
  rw [sub8176, sub8164]
  rfl
theorem sub8178 (p : Pattern) : d1393 (change p 163 (some 141)) = d5261 p := by
  change (if p 138 then d12 (change p 163 (some 141)) else d1391 (change p 163 (some 141))) = d5261 p
  rw [sub7979, sub8176]
  rfl
theorem sub8179 (p : Pattern) : d1394 (change p 163 (some 141)) = d5262 p := by
  change (if p 116 then d1393 (change p 163 (some 141)) else d1392 (change p 163 (some 141))) = d5262 p
  rw [sub8178, sub8177]
  rfl
theorem sub8180 (p : Pattern) : d1395 (change p 163 (some 141)) = d5263 p := by
  change (if p 115 then d1394 (change p 163 (some 141)) else d1366 (change p 163 (some 141))) = d5263 p
  rw [sub8179, sub8153]
  rfl
theorem sub8181 (p : Pattern) : d1396 (change p 163 (some 141)) = d5264 p := by
  change (if p 71 then d1395 (change p 163 (some 141)) else d1236 (change p 163 (some 141))) = d5264 p
  rw [sub8180, sub8048]
  rfl
theorem sub8182 (p : Pattern) : d1397 (change p 163 (some 141)) = d5265 p := by
  change (if p 49 then d1396 (change p 163 (some 141)) else d1357 (change p 163 (some 141))) = d5265 p
  rw [sub8181, sub8144]
  rfl
theorem sub8183 (p : Pattern) : d1398 (change p 163 (some 141)) = d5266 p := by
  change (if p 48 then d1397 (change p 163 (some 141)) else d1345 (change p 163 (some 141))) = d5266 p
  rw [sub8182, sub8127]
  rfl
theorem sub8184 (p : Pattern) : d0 (change p 224 (some 246)) = d0 p := by
  rfl
theorem sub8185 (p : Pattern) : d12 (change p 224 (some 246)) = d12 p := by
  rfl
theorem sub8186 (p : Pattern) : d13 (change p 224 (some 246)) = d13 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d0 (change p 224 (some 246))) = d13 p
  rw [sub8185, sub8184]
  rfl
theorem sub8187 (p : Pattern) : d14 (change p 224 (some 246)) = d13 p := by
  change d13 (change p 224 (some 246)) = d13 p
  exact sub8186 p
theorem sub8188 (p : Pattern) : d2184 (change p 224 (some 246)) = d13 p := by
  change d14 (change p 224 (some 246)) = d13 p
  exact sub8187 p
theorem sub8189 (p : Pattern) : d2185 (change p 224 (some 246)) = d13 p := by
  change d14 (change p 224 (some 246)) = d13 p
  exact sub8187 p
theorem sub8190 (p : Pattern) : d2186 (change p 224 (some 246)) = d13 p := by
  change (if p 204 then d2185 (change p 224 (some 246)) else d2184 (change p 224 (some 246))) = d13 p
  rw [sub8189, sub8188]
  simp only [ite_self]
theorem sub8191 (p : Pattern) : d2187 (change p 224 (some 246)) = d5270 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2185 (change p 224 (some 246))) = d5270 p
  rw [sub8185, sub8189]
  rfl
theorem sub8192 (p : Pattern) : d2188 (change p 224 (some 246)) = d5271 p := by
  change (if p 182 then d2187 (change p 224 (some 246)) else d2186 (change p 224 (some 246))) = d5271 p
  rw [sub8191, sub8190]
  rfl
theorem sub8193 (p : Pattern) : d2189 (change p 224 (some 246)) = d13 p := by
  change d14 (change p 224 (some 246)) = d13 p
  exact sub8187 p
theorem sub8194 (p : Pattern) : d2190 (change p 224 (some 246)) = d13 p := by
  change (if p 204 then d2185 (change p 224 (some 246)) else d2189 (change p 224 (some 246))) = d13 p
  rw [sub8189, sub8193]
  simp only [ite_self]
theorem sub8195 (p : Pattern) : d2191 (change p 224 (some 246)) = d5271 p := by
  change (if p 182 then d2187 (change p 224 (some 246)) else d2190 (change p 224 (some 246))) = d5271 p
  rw [sub8191, sub8194]
  rfl
theorem sub8196 (p : Pattern) : d2192 (change p 224 (some 246)) = d5271 p := by
  change (if p 163 then d2191 (change p 224 (some 246)) else d2188 (change p 224 (some 246))) = d5271 p
  rw [sub8195, sub8192]
  simp only [ite_self]
theorem sub8197 (p : Pattern) : d2193 (change p 224 (some 246)) = d13 p := by
  change d14 (change p 224 (some 246)) = d13 p
  exact sub8187 p
theorem sub8198 (p : Pattern) : d2194 (change p 224 (some 246)) = d13 p := by
  change (if p 204 then d2185 (change p 224 (some 246)) else d2193 (change p 224 (some 246))) = d13 p
  rw [sub8189, sub8197]
  simp only [ite_self]
theorem sub8199 (p : Pattern) : d2195 (change p 224 (some 246)) = d5271 p := by
  change (if p 182 then d2187 (change p 224 (some 246)) else d2194 (change p 224 (some 246))) = d5271 p
  rw [sub8191, sub8198]
  rfl
theorem sub8200 (p : Pattern) : d4 (change p 224 (some 246)) = d4 p := by
  rfl
theorem sub8201 (p : Pattern) : d17 (change p 224 (some 246)) = d17 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d4 (change p 224 (some 246))) = d17 p
  rw [sub8185, sub8200]
  rfl
theorem sub8202 (p : Pattern) : d18 (change p 224 (some 246)) = d17 p := by
  change d17 (change p 224 (some 246)) = d17 p
  exact sub8201 p
theorem sub8203 (p : Pattern) : d2196 (change p 224 (some 246)) = d17 p := by
  change d18 (change p 224 (some 246)) = d17 p
  exact sub8202 p
theorem sub8204 (p : Pattern) : d2197 (change p 224 (some 246)) = d5272 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2196 (change p 224 (some 246))) = d5272 p
  rw [sub8185, sub8203]
  rfl
theorem sub8205 (p : Pattern) : d2198 (change p 224 (some 246)) = d5273 p := by
  change (if p 182 then d2197 (change p 224 (some 246)) else d2196 (change p 224 (some 246))) = d5273 p
  rw [sub8204, sub8203]
  rfl
theorem sub8206 (p : Pattern) : d2199 (change p 224 (some 246)) = d5274 p := by
  change (if p 163 then d2198 (change p 224 (some 246)) else d2195 (change p 224 (some 246))) = d5274 p
  rw [sub8205, sub8199]
  rfl
theorem sub8207 (p : Pattern) : d2200 (change p 224 (some 246)) = d5275 p := by
  change (if p 162 then d2199 (change p 224 (some 246)) else d2192 (change p 224 (some 246))) = d5275 p
  rw [sub8206, sub8196]
  rfl
theorem sub8208 (p : Pattern) : d2201 (change p 224 (some 246)) = d5271 p := by
  change (if p 182 then d2187 (change p 224 (some 246)) else d2185 (change p 224 (some 246))) = d5271 p
  rw [sub8191, sub8189]
  rfl
theorem sub8209 (p : Pattern) : d2202 (change p 224 (some 246)) = d5274 p := by
  change (if p 163 then d2198 (change p 224 (some 246)) else d2201 (change p 224 (some 246))) = d5274 p
  rw [sub8205, sub8208]
  rfl
theorem sub8210 (p : Pattern) : d9 (change p 224 (some 246)) = d9 p := by
  rfl
theorem sub8211 (p : Pattern) : d23 (change p 224 (some 246)) = d23 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d9 (change p 224 (some 246))) = d23 p
  rw [sub8185, sub8210]
  rfl
theorem sub8212 (p : Pattern) : d24 (change p 224 (some 246)) = d23 p := by
  change d23 (change p 224 (some 246)) = d23 p
  exact sub8211 p
theorem sub8213 (p : Pattern) : d2203 (change p 224 (some 246)) = d23 p := by
  change d24 (change p 224 (some 246)) = d23 p
  exact sub8212 p
theorem sub8214 (p : Pattern) : d2204 (change p 224 (some 246)) = d5276 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2203 (change p 224 (some 246))) = d5276 p
  rw [sub8185, sub8213]
  rfl
theorem sub8215 (p : Pattern) : d2205 (change p 224 (some 246)) = d5277 p := by
  change (if p 182 then d2204 (change p 224 (some 246)) else d2203 (change p 224 (some 246))) = d5277 p
  rw [sub8214, sub8213]
  rfl
theorem sub8216 (p : Pattern) : d2206 (change p 224 (some 246)) = d5278 p := by
  change (if p 163 then d12 (change p 224 (some 246)) else d2205 (change p 224 (some 246))) = d5278 p
  rw [sub8185, sub8215]
  rfl
theorem sub8217 (p : Pattern) : d2207 (change p 224 (some 246)) = d5279 p := by
  change (if p 162 then d2206 (change p 224 (some 246)) else d2202 (change p 224 (some 246))) = d5279 p
  rw [sub8216, sub8209]
  rfl
theorem sub8218 (p : Pattern) : d2208 (change p 224 (some 246)) = d5280 p := by
  change (if p 161 then d2207 (change p 224 (some 246)) else d2200 (change p 224 (some 246))) = d5280 p
  rw [sub8217, sub8207]
  rfl
theorem sub8219 (p : Pattern) : d2 (change p 224 (some 246)) = d2 p := by
  rfl
theorem sub8220 (p : Pattern) : d30 (change p 224 (some 246)) = d30 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d2 (change p 224 (some 246))) = d30 p
  rw [sub8185, sub8219]
  rfl
theorem sub8221 (p : Pattern) : d31 (change p 224 (some 246)) = d30 p := by
  change d30 (change p 224 (some 246)) = d30 p
  exact sub8220 p
theorem sub8222 (p : Pattern) : d2209 (change p 224 (some 246)) = d30 p := by
  change d31 (change p 224 (some 246)) = d30 p
  exact sub8221 p
theorem sub8223 (p : Pattern) : d2210 (change p 224 (some 246)) = d5281 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2209 (change p 224 (some 246))) = d5281 p
  rw [sub8185, sub8222]
  rfl
theorem sub8224 (p : Pattern) : d2211 (change p 224 (some 246)) = d5282 p := by
  change (if p 182 then d2210 (change p 224 (some 246)) else d2185 (change p 224 (some 246))) = d5282 p
  rw [sub8223, sub8189]
  rfl
theorem sub8225 (p : Pattern) : d6 (change p 224 (some 246)) = d6 p := by
  rfl
theorem sub8226 (p : Pattern) : d34 (change p 224 (some 246)) = d34 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d6 (change p 224 (some 246))) = d34 p
  rw [sub8185, sub8225]
  rfl
theorem sub8227 (p : Pattern) : d35 (change p 224 (some 246)) = d34 p := by
  change d34 (change p 224 (some 246)) = d34 p
  exact sub8226 p
theorem sub8228 (p : Pattern) : d2212 (change p 224 (some 246)) = d34 p := by
  change d35 (change p 224 (some 246)) = d34 p
  exact sub8227 p
theorem sub8229 (p : Pattern) : d2213 (change p 224 (some 246)) = d5283 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2212 (change p 224 (some 246))) = d5283 p
  rw [sub8185, sub8228]
  rfl
theorem sub8230 (p : Pattern) : d2214 (change p 224 (some 246)) = d5284 p := by
  change (if p 182 then d2213 (change p 224 (some 246)) else d2185 (change p 224 (some 246))) = d5284 p
  rw [sub8229, sub8189]
  rfl
theorem sub8231 (p : Pattern) : d2215 (change p 224 (some 246)) = d5285 p := by
  change (if p 163 then d2214 (change p 224 (some 246)) else d2211 (change p 224 (some 246))) = d5285 p
  rw [sub8230, sub8224]
  rfl
theorem sub8232 (p : Pattern) : d11 (change p 224 (some 246)) = d11 p := by
  rfl
theorem sub8233 (p : Pattern) : d39 (change p 224 (some 246)) = d39 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d11 (change p 224 (some 246))) = d39 p
  rw [sub8185, sub8232]
  rfl
theorem sub8234 (p : Pattern) : d40 (change p 224 (some 246)) = d39 p := by
  change d39 (change p 224 (some 246)) = d39 p
  exact sub8233 p
theorem sub8235 (p : Pattern) : d2216 (change p 224 (some 246)) = d39 p := by
  change d40 (change p 224 (some 246)) = d39 p
  exact sub8234 p
theorem sub8236 (p : Pattern) : d2217 (change p 224 (some 246)) = d5286 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2216 (change p 224 (some 246))) = d5286 p
  rw [sub8185, sub8235]
  rfl
theorem sub8237 (p : Pattern) : d2218 (change p 224 (some 246)) = d5287 p := by
  change (if p 182 then d2217 (change p 224 (some 246)) else d2185 (change p 224 (some 246))) = d5287 p
  rw [sub8236, sub8189]
  rfl
theorem sub8238 (p : Pattern) : d2219 (change p 224 (some 246)) = d5288 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2196 (change p 224 (some 246))) = d5288 p
  rw [sub8185, sub8203]
  rfl
theorem sub8239 (p : Pattern) : d2220 (change p 224 (some 246)) = d5289 p := by
  change (if p 163 then d2219 (change p 224 (some 246)) else d2218 (change p 224 (some 246))) = d5289 p
  rw [sub8238, sub8237]
  rfl
theorem sub8240 (p : Pattern) : d2221 (change p 224 (some 246)) = d5290 p := by
  change (if p 162 then d2220 (change p 224 (some 246)) else d2215 (change p 224 (some 246))) = d5290 p
  rw [sub8239, sub8231]
  rfl
theorem sub8241 (p : Pattern) : d2222 (change p 224 (some 246)) = d5291 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2185 (change p 224 (some 246))) = d5291 p
  rw [sub8185, sub8189]
  rfl
theorem sub8242 (p : Pattern) : d2223 (change p 224 (some 246)) = d5292 p := by
  change (if p 163 then d2219 (change p 224 (some 246)) else d2222 (change p 224 (some 246))) = d5292 p
  rw [sub8238, sub8241]
  rfl
theorem sub8243 (p : Pattern) : d2224 (change p 224 (some 246)) = d5293 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2203 (change p 224 (some 246))) = d5293 p
  rw [sub8185, sub8213]
  rfl
theorem sub8244 (p : Pattern) : d2225 (change p 224 (some 246)) = d5294 p := by
  change (if p 163 then d12 (change p 224 (some 246)) else d2224 (change p 224 (some 246))) = d5294 p
  rw [sub8185, sub8243]
  rfl
theorem sub8245 (p : Pattern) : d2226 (change p 224 (some 246)) = d5295 p := by
  change (if p 162 then d2225 (change p 224 (some 246)) else d2223 (change p 224 (some 246))) = d5295 p
  rw [sub8244, sub8242]
  rfl
theorem sub8246 (p : Pattern) : d2227 (change p 224 (some 246)) = d5296 p := by
  change (if p 161 then d2226 (change p 224 (some 246)) else d2221 (change p 224 (some 246))) = d5296 p
  rw [sub8245, sub8240]
  rfl
theorem sub8247 (p : Pattern) : d2228 (change p 224 (some 246)) = d5297 p := by
  change (if p 160 then d2227 (change p 224 (some 246)) else d2208 (change p 224 (some 246))) = d5297 p
  rw [sub8246, sub8218]
  rfl
theorem sub8248 (p : Pattern) : d2229 (change p 224 (some 246)) = d13 p := by
  change d14 (change p 224 (some 246)) = d13 p
  exact sub8187 p
theorem sub8249 (p : Pattern) : d2230 (change p 224 (some 246)) = d13 p := by
  change (if p 204 then d2185 (change p 224 (some 246)) else d2229 (change p 224 (some 246))) = d13 p
  rw [sub8189, sub8248]
  simp only [ite_self]
theorem sub8250 (p : Pattern) : d2231 (change p 224 (some 246)) = d5271 p := by
  change (if p 182 then d2187 (change p 224 (some 246)) else d2230 (change p 224 (some 246))) = d5271 p
  rw [sub8191, sub8249]
  rfl
theorem sub8251 (p : Pattern) : d2232 (change p 224 (some 246)) = d5298 p := by
  change (if p 182 then d2210 (change p 224 (some 246)) else d2209 (change p 224 (some 246))) = d5298 p
  rw [sub8223, sub8222]
  rfl
theorem sub8252 (p : Pattern) : d2233 (change p 224 (some 246)) = d5299 p := by
  change (if p 163 then d2232 (change p 224 (some 246)) else d2231 (change p 224 (some 246))) = d5299 p
  rw [sub8251, sub8250]
  rfl
theorem sub8253 (p : Pattern) : d2234 (change p 224 (some 246)) = d5300 p := by
  change (if p 163 then d2205 (change p 224 (some 246)) else d2198 (change p 224 (some 246))) = d5300 p
  rw [sub8215, sub8205]
  rfl
theorem sub8254 (p : Pattern) : d2235 (change p 224 (some 246)) = d5301 p := by
  change (if p 162 then d2234 (change p 224 (some 246)) else d2233 (change p 224 (some 246))) = d5301 p
  rw [sub8253, sub8252]
  rfl
theorem sub8255 (p : Pattern) : d10 (change p 224 (some 246)) = d10 p := by
  rfl
theorem sub8256 (p : Pattern) : d57 (change p 224 (some 246)) = d57 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d10 (change p 224 (some 246))) = d57 p
  rw [sub8185, sub8255]
  rfl
theorem sub8257 (p : Pattern) : d58 (change p 224 (some 246)) = d57 p := by
  change d57 (change p 224 (some 246)) = d57 p
  exact sub8256 p
theorem sub8258 (p : Pattern) : d2236 (change p 224 (some 246)) = d57 p := by
  change d58 (change p 224 (some 246)) = d57 p
  exact sub8257 p
theorem sub8259 (p : Pattern) : d2237 (change p 224 (some 246)) = d5302 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2236 (change p 224 (some 246))) = d5302 p
  rw [sub8185, sub8258]
  rfl
theorem sub8260 (p : Pattern) : d2238 (change p 224 (some 246)) = d5303 p := by
  change (if p 182 then d2237 (change p 224 (some 246)) else d2236 (change p 224 (some 246))) = d5303 p
  rw [sub8259, sub8258]
  rfl
theorem sub8261 (p : Pattern) : d2239 (change p 224 (some 246)) = d5304 p := by
  change (if p 163 then d2238 (change p 224 (some 246)) else d2198 (change p 224 (some 246))) = d5304 p
  rw [sub8260, sub8205]
  rfl
theorem sub8262 (p : Pattern) : d2240 (change p 224 (some 246)) = d5305 p := by
  change (if p 182 then d2217 (change p 224 (some 246)) else d2216 (change p 224 (some 246))) = d5305 p
  rw [sub8236, sub8235]
  rfl
theorem sub8263 (p : Pattern) : d2241 (change p 224 (some 246)) = d5306 p := by
  change (if p 163 then d12 (change p 224 (some 246)) else d2240 (change p 224 (some 246))) = d5306 p
  rw [sub8185, sub8262]
  rfl
theorem sub8264 (p : Pattern) : d2242 (change p 224 (some 246)) = d5307 p := by
  change (if p 162 then d2241 (change p 224 (some 246)) else d2239 (change p 224 (some 246))) = d5307 p
  rw [sub8263, sub8261]
  rfl
theorem sub8265 (p : Pattern) : d2243 (change p 224 (some 246)) = d5308 p := by
  change (if p 161 then d2242 (change p 224 (some 246)) else d2235 (change p 224 (some 246))) = d5308 p
  rw [sub8264, sub8254]
  rfl
theorem sub8266 (p : Pattern) : d2244 (change p 224 (some 246)) = d5309 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2209 (change p 224 (some 246))) = d5309 p
  rw [sub8185, sub8222]
  rfl
theorem sub8267 (p : Pattern) : d2245 (change p 224 (some 246)) = d5310 p := by
  change (if p 163 then d2244 (change p 224 (some 246)) else d2214 (change p 224 (some 246))) = d5310 p
  rw [sub8266, sub8230]
  rfl
theorem sub8268 (p : Pattern) : d2246 (change p 224 (some 246)) = d5311 p := by
  change (if p 163 then d2224 (change p 224 (some 246)) else d2219 (change p 224 (some 246))) = d5311 p
  rw [sub8243, sub8238]
  rfl
theorem sub8269 (p : Pattern) : d2247 (change p 224 (some 246)) = d5312 p := by
  change (if p 162 then d2246 (change p 224 (some 246)) else d2245 (change p 224 (some 246))) = d5312 p
  rw [sub8268, sub8267]
  rfl
theorem sub8270 (p : Pattern) : d2248 (change p 224 (some 246)) = d5313 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2236 (change p 224 (some 246))) = d5313 p
  rw [sub8185, sub8258]
  rfl
theorem sub8271 (p : Pattern) : d2249 (change p 224 (some 246)) = d5314 p := by
  change (if p 163 then d2248 (change p 224 (some 246)) else d2219 (change p 224 (some 246))) = d5314 p
  rw [sub8270, sub8238]
  rfl
theorem sub8272 (p : Pattern) : d2250 (change p 224 (some 246)) = d5315 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2216 (change p 224 (some 246))) = d5315 p
  rw [sub8185, sub8235]
  rfl
theorem sub8273 (p : Pattern) : d2251 (change p 224 (some 246)) = d5316 p := by
  change (if p 163 then d12 (change p 224 (some 246)) else d2250 (change p 224 (some 246))) = d5316 p
  rw [sub8185, sub8272]
  rfl
theorem sub8274 (p : Pattern) : d2252 (change p 224 (some 246)) = d5317 p := by
  change (if p 162 then d2251 (change p 224 (some 246)) else d2249 (change p 224 (some 246))) = d5317 p
  rw [sub8273, sub8271]
  rfl
theorem sub8275 (p : Pattern) : d2253 (change p 224 (some 246)) = d5318 p := by
  change (if p 161 then d2252 (change p 224 (some 246)) else d2247 (change p 224 (some 246))) = d5318 p
  rw [sub8274, sub8269]
  rfl
theorem sub8276 (p : Pattern) : d2254 (change p 224 (some 246)) = d5319 p := by
  change (if p 160 then d2253 (change p 224 (some 246)) else d2243 (change p 224 (some 246))) = d5319 p
  rw [sub8275, sub8265]
  rfl
theorem sub8277 (p : Pattern) : d2255 (change p 224 (some 246)) = d5320 p := by
  change (if p 141 then d2254 (change p 224 (some 246)) else d2228 (change p 224 (some 246))) = d5320 p
  rw [sub8276, sub8247]
  rfl
theorem sub8278 (p : Pattern) : d2256 (change p 224 (some 246)) = d5275 p := by
  change (if p 162 then d2202 (change p 224 (some 246)) else d2201 (change p 224 (some 246))) = d5275 p
  rw [sub8209, sub8208]
  rfl
theorem sub8279 (p : Pattern) : d2257 (change p 224 (some 246)) = d5280 p := by
  change (if p 161 then d2207 (change p 224 (some 246)) else d2256 (change p 224 (some 246))) = d5280 p
  rw [sub8217, sub8278]
  rfl
end NetHack.Sokoban22Refined85
