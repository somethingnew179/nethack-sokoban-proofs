/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions76
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub9240 (p : Pattern) : d2185 (change p 224 (some 225)) = d14 p := by
  change d14 (change p 224 (some 225)) = d14 p
  exact sub9238 p
theorem sub9241 (p : Pattern) : d2186 (change p 224 (some 225)) = d14 p := by
  change (if p 204 then d2185 (change p 224 (some 225)) else d2184 (change p 224 (some 225))) = d14 p
  rw [sub9240, sub9239]
  simp only [ite_self]
theorem sub9242 (p : Pattern) : d2187 (change p 224 (some 225)) = d15 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2185 (change p 224 (some 225))) = d15 p
  rw [sub9236, sub9240]
  rfl
theorem sub9243 (p : Pattern) : d2188 (change p 224 (some 225)) = d16 p := by
  change (if p 182 then d2187 (change p 224 (some 225)) else d2186 (change p 224 (some 225))) = d16 p
  rw [sub9242, sub9241]
  rfl
theorem sub9244 (p : Pattern) : d2189 (change p 224 (some 225)) = d14 p := by
  change d14 (change p 224 (some 225)) = d14 p
  exact sub9238 p
theorem sub9245 (p : Pattern) : d2190 (change p 224 (some 225)) = d14 p := by
  change (if p 204 then d2185 (change p 224 (some 225)) else d2189 (change p 224 (some 225))) = d14 p
  rw [sub9240, sub9244]
  simp only [ite_self]
theorem sub9246 (p : Pattern) : d2191 (change p 224 (some 225)) = d16 p := by
  change (if p 182 then d2187 (change p 224 (some 225)) else d2190 (change p 224 (some 225))) = d16 p
  rw [sub9242, sub9245]
  rfl
theorem sub9247 (p : Pattern) : d2192 (change p 224 (some 225)) = d16 p := by
  change (if p 163 then d2191 (change p 224 (some 225)) else d2188 (change p 224 (some 225))) = d16 p
  rw [sub9246, sub9243]
  simp only [ite_self]
theorem sub9248 (p : Pattern) : d2193 (change p 224 (some 225)) = d14 p := by
  change d14 (change p 224 (some 225)) = d14 p
  exact sub9238 p
theorem sub9249 (p : Pattern) : d2194 (change p 224 (some 225)) = d14 p := by
  change (if p 204 then d2185 (change p 224 (some 225)) else d2193 (change p 224 (some 225))) = d14 p
  rw [sub9240, sub9248]
  simp only [ite_self]
theorem sub9250 (p : Pattern) : d2195 (change p 224 (some 225)) = d16 p := by
  change (if p 182 then d2187 (change p 224 (some 225)) else d2194 (change p 224 (some 225))) = d16 p
  rw [sub9242, sub9249]
  rfl
theorem sub9251 (p : Pattern) : d4 (change p 224 (some 225)) = d4 p := by
  rfl
theorem sub9252 (p : Pattern) : d17 (change p 224 (some 225)) = d17 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d4 (change p 224 (some 225))) = d17 p
  rw [sub9236, sub9251]
  rfl
theorem sub9253 (p : Pattern) : d18 (change p 224 (some 225)) = d18 p := by
  change (if p 246 then d17 (change p 224 (some 225)) else d4 (change p 224 (some 225))) = d18 p
  rw [sub9252, sub9251]
  rfl
theorem sub9254 (p : Pattern) : d2196 (change p 224 (some 225)) = d18 p := by
  change d18 (change p 224 (some 225)) = d18 p
  exact sub9253 p
theorem sub9255 (p : Pattern) : d2197 (change p 224 (some 225)) = d19 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2196 (change p 224 (some 225))) = d19 p
  rw [sub9236, sub9254]
  rfl
theorem sub9256 (p : Pattern) : d2198 (change p 224 (some 225)) = d20 p := by
  change (if p 182 then d2197 (change p 224 (some 225)) else d2196 (change p 224 (some 225))) = d20 p
  rw [sub9255, sub9254]
  rfl
theorem sub9257 (p : Pattern) : d2199 (change p 224 (some 225)) = d21 p := by
  change (if p 163 then d2198 (change p 224 (some 225)) else d2195 (change p 224 (some 225))) = d21 p
  rw [sub9256, sub9250]
  rfl
theorem sub9258 (p : Pattern) : d2200 (change p 224 (some 225)) = d22 p := by
  change (if p 162 then d2199 (change p 224 (some 225)) else d2192 (change p 224 (some 225))) = d22 p
  rw [sub9257, sub9247]
  rfl
theorem sub9259 (p : Pattern) : d2201 (change p 224 (some 225)) = d16 p := by
  change (if p 182 then d2187 (change p 224 (some 225)) else d2185 (change p 224 (some 225))) = d16 p
  rw [sub9242, sub9240]
  rfl
theorem sub9260 (p : Pattern) : d2202 (change p 224 (some 225)) = d21 p := by
  change (if p 163 then d2198 (change p 224 (some 225)) else d2201 (change p 224 (some 225))) = d21 p
  rw [sub9256, sub9259]
  rfl
theorem sub9261 (p : Pattern) : d9 (change p 224 (some 225)) = d9 p := by
  rfl
theorem sub9262 (p : Pattern) : d23 (change p 224 (some 225)) = d23 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d9 (change p 224 (some 225))) = d23 p
  rw [sub9236, sub9261]
  rfl
theorem sub9263 (p : Pattern) : d24 (change p 224 (some 225)) = d24 p := by
  change (if p 246 then d23 (change p 224 (some 225)) else d9 (change p 224 (some 225))) = d24 p
  rw [sub9262, sub9261]
  rfl
theorem sub9264 (p : Pattern) : d2203 (change p 224 (some 225)) = d24 p := by
  change d24 (change p 224 (some 225)) = d24 p
  exact sub9263 p
theorem sub9265 (p : Pattern) : d2204 (change p 224 (some 225)) = d25 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2203 (change p 224 (some 225))) = d25 p
  rw [sub9236, sub9264]
  rfl
theorem sub9266 (p : Pattern) : d2205 (change p 224 (some 225)) = d26 p := by
  change (if p 182 then d2204 (change p 224 (some 225)) else d2203 (change p 224 (some 225))) = d26 p
  rw [sub9265, sub9264]
  rfl
theorem sub9267 (p : Pattern) : d2206 (change p 224 (some 225)) = d27 p := by
  change (if p 163 then d12 (change p 224 (some 225)) else d2205 (change p 224 (some 225))) = d27 p
  rw [sub9236, sub9266]
  rfl
theorem sub9268 (p : Pattern) : d2207 (change p 224 (some 225)) = d28 p := by
  change (if p 162 then d2206 (change p 224 (some 225)) else d2202 (change p 224 (some 225))) = d28 p
  rw [sub9267, sub9260]
  rfl
theorem sub9269 (p : Pattern) : d2208 (change p 224 (some 225)) = d29 p := by
  change (if p 161 then d2207 (change p 224 (some 225)) else d2200 (change p 224 (some 225))) = d29 p
  rw [sub9268, sub9258]
  rfl
theorem sub9270 (p : Pattern) : d2 (change p 224 (some 225)) = d2 p := by
  rfl
theorem sub9271 (p : Pattern) : d30 (change p 224 (some 225)) = d30 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d2 (change p 224 (some 225))) = d30 p
  rw [sub9236, sub9270]
  rfl
theorem sub9272 (p : Pattern) : d31 (change p 224 (some 225)) = d31 p := by
  change (if p 246 then d30 (change p 224 (some 225)) else d2 (change p 224 (some 225))) = d31 p
  rw [sub9271, sub9270]
  rfl
theorem sub9273 (p : Pattern) : d2209 (change p 224 (some 225)) = d31 p := by
  change d31 (change p 224 (some 225)) = d31 p
  exact sub9272 p
theorem sub9274 (p : Pattern) : d2210 (change p 224 (some 225)) = d32 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2209 (change p 224 (some 225))) = d32 p
  rw [sub9236, sub9273]
  rfl
theorem sub9275 (p : Pattern) : d2211 (change p 224 (some 225)) = d33 p := by
  change (if p 182 then d2210 (change p 224 (some 225)) else d2185 (change p 224 (some 225))) = d33 p
  rw [sub9274, sub9240]
  rfl
theorem sub9276 (p : Pattern) : d6 (change p 224 (some 225)) = d6 p := by
  rfl
theorem sub9277 (p : Pattern) : d34 (change p 224 (some 225)) = d34 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d6 (change p 224 (some 225))) = d34 p
  rw [sub9236, sub9276]
  rfl
theorem sub9278 (p : Pattern) : d35 (change p 224 (some 225)) = d35 p := by
  change (if p 246 then d34 (change p 224 (some 225)) else d6 (change p 224 (some 225))) = d35 p
  rw [sub9277, sub9276]
  rfl
theorem sub9279 (p : Pattern) : d2212 (change p 224 (some 225)) = d35 p := by
  change d35 (change p 224 (some 225)) = d35 p
  exact sub9278 p
theorem sub9280 (p : Pattern) : d2213 (change p 224 (some 225)) = d36 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2212 (change p 224 (some 225))) = d36 p
  rw [sub9236, sub9279]
  rfl
theorem sub9281 (p : Pattern) : d2214 (change p 224 (some 225)) = d37 p := by
  change (if p 182 then d2213 (change p 224 (some 225)) else d2185 (change p 224 (some 225))) = d37 p
  rw [sub9280, sub9240]
  rfl
theorem sub9282 (p : Pattern) : d2215 (change p 224 (some 225)) = d38 p := by
  change (if p 163 then d2214 (change p 224 (some 225)) else d2211 (change p 224 (some 225))) = d38 p
  rw [sub9281, sub9275]
  rfl
theorem sub9283 (p : Pattern) : d11 (change p 224 (some 225)) = d11 p := by
  rfl
theorem sub9284 (p : Pattern) : d39 (change p 224 (some 225)) = d39 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d11 (change p 224 (some 225))) = d39 p
  rw [sub9236, sub9283]
  rfl
theorem sub9285 (p : Pattern) : d40 (change p 224 (some 225)) = d40 p := by
  change (if p 246 then d39 (change p 224 (some 225)) else d11 (change p 224 (some 225))) = d40 p
  rw [sub9284, sub9283]
  rfl
theorem sub9286 (p : Pattern) : d2216 (change p 224 (some 225)) = d40 p := by
  change d40 (change p 224 (some 225)) = d40 p
  exact sub9285 p
theorem sub9287 (p : Pattern) : d2217 (change p 224 (some 225)) = d41 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2216 (change p 224 (some 225))) = d41 p
  rw [sub9236, sub9286]
  rfl
theorem sub9288 (p : Pattern) : d2218 (change p 224 (some 225)) = d42 p := by
  change (if p 182 then d2217 (change p 224 (some 225)) else d2185 (change p 224 (some 225))) = d42 p
  rw [sub9287, sub9240]
  rfl
theorem sub9289 (p : Pattern) : d2219 (change p 224 (some 225)) = d43 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2196 (change p 224 (some 225))) = d43 p
  rw [sub9236, sub9254]
  rfl
theorem sub9290 (p : Pattern) : d2220 (change p 224 (some 225)) = d44 p := by
  change (if p 163 then d2219 (change p 224 (some 225)) else d2218 (change p 224 (some 225))) = d44 p
  rw [sub9289, sub9288]
  rfl
theorem sub9291 (p : Pattern) : d2221 (change p 224 (some 225)) = d45 p := by
  change (if p 162 then d2220 (change p 224 (some 225)) else d2215 (change p 224 (some 225))) = d45 p
  rw [sub9290, sub9282]
  rfl
theorem sub9292 (p : Pattern) : d2222 (change p 224 (some 225)) = d46 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2185 (change p 224 (some 225))) = d46 p
  rw [sub9236, sub9240]
  rfl
theorem sub9293 (p : Pattern) : d2223 (change p 224 (some 225)) = d47 p := by
  change (if p 163 then d2219 (change p 224 (some 225)) else d2222 (change p 224 (some 225))) = d47 p
  rw [sub9289, sub9292]
  rfl
theorem sub9294 (p : Pattern) : d2224 (change p 224 (some 225)) = d48 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2203 (change p 224 (some 225))) = d48 p
  rw [sub9236, sub9264]
  rfl
theorem sub9295 (p : Pattern) : d2225 (change p 224 (some 225)) = d49 p := by
  change (if p 163 then d12 (change p 224 (some 225)) else d2224 (change p 224 (some 225))) = d49 p
  rw [sub9236, sub9294]
  rfl
theorem sub9296 (p : Pattern) : d2226 (change p 224 (some 225)) = d50 p := by
  change (if p 162 then d2225 (change p 224 (some 225)) else d2223 (change p 224 (some 225))) = d50 p
  rw [sub9295, sub9293]
  rfl
theorem sub9297 (p : Pattern) : d2227 (change p 224 (some 225)) = d51 p := by
  change (if p 161 then d2226 (change p 224 (some 225)) else d2221 (change p 224 (some 225))) = d51 p
  rw [sub9296, sub9291]
  rfl
theorem sub9298 (p : Pattern) : d2228 (change p 224 (some 225)) = d52 p := by
  change (if p 160 then d2227 (change p 224 (some 225)) else d2208 (change p 224 (some 225))) = d52 p
  rw [sub9297, sub9269]
  rfl
theorem sub9299 (p : Pattern) : d2229 (change p 224 (some 225)) = d14 p := by
  change d14 (change p 224 (some 225)) = d14 p
  exact sub9238 p
theorem sub9300 (p : Pattern) : d2230 (change p 224 (some 225)) = d14 p := by
  change (if p 204 then d2185 (change p 224 (some 225)) else d2229 (change p 224 (some 225))) = d14 p
  rw [sub9240, sub9299]
  simp only [ite_self]
theorem sub9301 (p : Pattern) : d2231 (change p 224 (some 225)) = d16 p := by
  change (if p 182 then d2187 (change p 224 (some 225)) else d2230 (change p 224 (some 225))) = d16 p
  rw [sub9242, sub9300]
  rfl
theorem sub9302 (p : Pattern) : d2232 (change p 224 (some 225)) = d53 p := by
  change (if p 182 then d2210 (change p 224 (some 225)) else d2209 (change p 224 (some 225))) = d53 p
  rw [sub9274, sub9273]
  rfl
theorem sub9303 (p : Pattern) : d2233 (change p 224 (some 225)) = d54 p := by
  change (if p 163 then d2232 (change p 224 (some 225)) else d2231 (change p 224 (some 225))) = d54 p
  rw [sub9302, sub9301]
  rfl
theorem sub9304 (p : Pattern) : d2234 (change p 224 (some 225)) = d55 p := by
  change (if p 163 then d2205 (change p 224 (some 225)) else d2198 (change p 224 (some 225))) = d55 p
  rw [sub9266, sub9256]
  rfl
theorem sub9305 (p : Pattern) : d2235 (change p 224 (some 225)) = d56 p := by
  change (if p 162 then d2234 (change p 224 (some 225)) else d2233 (change p 224 (some 225))) = d56 p
  rw [sub9304, sub9303]
  rfl
theorem sub9306 (p : Pattern) : d10 (change p 224 (some 225)) = d10 p := by
  rfl
theorem sub9307 (p : Pattern) : d57 (change p 224 (some 225)) = d57 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d10 (change p 224 (some 225))) = d57 p
  rw [sub9236, sub9306]
  rfl
theorem sub9308 (p : Pattern) : d58 (change p 224 (some 225)) = d58 p := by
  change (if p 246 then d57 (change p 224 (some 225)) else d10 (change p 224 (some 225))) = d58 p
  rw [sub9307, sub9306]
  rfl
theorem sub9309 (p : Pattern) : d2236 (change p 224 (some 225)) = d58 p := by
  change d58 (change p 224 (some 225)) = d58 p
  exact sub9308 p
theorem sub9310 (p : Pattern) : d2237 (change p 224 (some 225)) = d59 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2236 (change p 224 (some 225))) = d59 p
  rw [sub9236, sub9309]
  rfl
theorem sub9311 (p : Pattern) : d2238 (change p 224 (some 225)) = d60 p := by
  change (if p 182 then d2237 (change p 224 (some 225)) else d2236 (change p 224 (some 225))) = d60 p
  rw [sub9310, sub9309]
  rfl
theorem sub9312 (p : Pattern) : d2239 (change p 224 (some 225)) = d61 p := by
  change (if p 163 then d2238 (change p 224 (some 225)) else d2198 (change p 224 (some 225))) = d61 p
  rw [sub9311, sub9256]
  rfl
theorem sub9313 (p : Pattern) : d2240 (change p 224 (some 225)) = d62 p := by
  change (if p 182 then d2217 (change p 224 (some 225)) else d2216 (change p 224 (some 225))) = d62 p
  rw [sub9287, sub9286]
  rfl
theorem sub9314 (p : Pattern) : d2241 (change p 224 (some 225)) = d63 p := by
  change (if p 163 then d12 (change p 224 (some 225)) else d2240 (change p 224 (some 225))) = d63 p
  rw [sub9236, sub9313]
  rfl
theorem sub9315 (p : Pattern) : d2242 (change p 224 (some 225)) = d64 p := by
  change (if p 162 then d2241 (change p 224 (some 225)) else d2239 (change p 224 (some 225))) = d64 p
  rw [sub9314, sub9312]
  rfl
theorem sub9316 (p : Pattern) : d2243 (change p 224 (some 225)) = d65 p := by
  change (if p 161 then d2242 (change p 224 (some 225)) else d2235 (change p 224 (some 225))) = d65 p
  rw [sub9315, sub9305]
  rfl
theorem sub9317 (p : Pattern) : d2244 (change p 224 (some 225)) = d66 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2209 (change p 224 (some 225))) = d66 p
  rw [sub9236, sub9273]
  rfl
theorem sub9318 (p : Pattern) : d2245 (change p 224 (some 225)) = d67 p := by
  change (if p 163 then d2244 (change p 224 (some 225)) else d2214 (change p 224 (some 225))) = d67 p
  rw [sub9317, sub9281]
  rfl
theorem sub9319 (p : Pattern) : d2246 (change p 224 (some 225)) = d68 p := by
  change (if p 163 then d2224 (change p 224 (some 225)) else d2219 (change p 224 (some 225))) = d68 p
  rw [sub9294, sub9289]
  rfl
theorem sub9320 (p : Pattern) : d2247 (change p 224 (some 225)) = d69 p := by
  change (if p 162 then d2246 (change p 224 (some 225)) else d2245 (change p 224 (some 225))) = d69 p
  rw [sub9319, sub9318]
  rfl
theorem sub9321 (p : Pattern) : d2248 (change p 224 (some 225)) = d70 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2236 (change p 224 (some 225))) = d70 p
  rw [sub9236, sub9309]
  rfl
theorem sub9322 (p : Pattern) : d2249 (change p 224 (some 225)) = d71 p := by
  change (if p 163 then d2248 (change p 224 (some 225)) else d2219 (change p 224 (some 225))) = d71 p
  rw [sub9321, sub9289]
  rfl
theorem sub9323 (p : Pattern) : d2250 (change p 224 (some 225)) = d72 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2216 (change p 224 (some 225))) = d72 p
  rw [sub9236, sub9286]
  rfl
theorem sub9324 (p : Pattern) : d2251 (change p 224 (some 225)) = d73 p := by
  change (if p 163 then d12 (change p 224 (some 225)) else d2250 (change p 224 (some 225))) = d73 p
  rw [sub9236, sub9323]
  rfl
theorem sub9325 (p : Pattern) : d2252 (change p 224 (some 225)) = d74 p := by
  change (if p 162 then d2251 (change p 224 (some 225)) else d2249 (change p 224 (some 225))) = d74 p
  rw [sub9324, sub9322]
  rfl
theorem sub9326 (p : Pattern) : d2253 (change p 224 (some 225)) = d75 p := by
  change (if p 161 then d2252 (change p 224 (some 225)) else d2247 (change p 224 (some 225))) = d75 p
  rw [sub9325, sub9320]
  rfl
theorem sub9327 (p : Pattern) : d2254 (change p 224 (some 225)) = d76 p := by
  change (if p 160 then d2253 (change p 224 (some 225)) else d2243 (change p 224 (some 225))) = d76 p
  rw [sub9326, sub9316]
  rfl
theorem sub9328 (p : Pattern) : d2255 (change p 224 (some 225)) = d77 p := by
  change (if p 141 then d2254 (change p 224 (some 225)) else d2228 (change p 224 (some 225))) = d77 p
  rw [sub9327, sub9298]
  rfl
theorem sub9329 (p : Pattern) : d2256 (change p 224 (some 225)) = d22 p := by
  change (if p 162 then d2202 (change p 224 (some 225)) else d2201 (change p 224 (some 225))) = d22 p
  rw [sub9260, sub9259]
  rfl
theorem sub9330 (p : Pattern) : d2257 (change p 224 (some 225)) = d29 p := by
  change (if p 161 then d2207 (change p 224 (some 225)) else d2256 (change p 224 (some 225))) = d29 p
  rw [sub9268, sub9329]
  rfl
theorem sub9331 (p : Pattern) : d2258 (change p 224 (some 225)) = d78 p := by
  change (if p 182 then d2213 (change p 224 (some 225)) else d2212 (change p 224 (some 225))) = d78 p
  rw [sub9280, sub9279]
  rfl
theorem sub9332 (p : Pattern) : d2259 (change p 224 (some 225)) = d79 p := by
  change (if p 163 then d2258 (change p 224 (some 225)) else d2232 (change p 224 (some 225))) = d79 p
  rw [sub9331, sub9302]
  rfl
theorem sub9333 (p : Pattern) : d2260 (change p 224 (some 225)) = d80 p := by
  change (if p 162 then d2241 (change p 224 (some 225)) else d2259 (change p 224 (some 225))) = d80 p
  rw [sub9314, sub9332]
  rfl
theorem sub9334 (p : Pattern) : d2261 (change p 224 (some 225)) = d81 p := by
  change (if p 161 then d12 (change p 224 (some 225)) else d2260 (change p 224 (some 225))) = d81 p
  rw [sub9236, sub9333]
  rfl
theorem sub9335 (p : Pattern) : d2262 (change p 224 (some 225)) = d82 p := by
  change (if p 160 then d2261 (change p 224 (some 225)) else d2257 (change p 224 (some 225))) = d82 p
  rw [sub9334, sub9330]
  rfl
theorem sub9336 (p : Pattern) : d2263 (change p 224 (some 225)) = d54 p := by
  change (if p 163 then d2232 (change p 224 (some 225)) else d2201 (change p 224 (some 225))) = d54 p
  rw [sub9302, sub9259]
  rfl
theorem sub9337 (p : Pattern) : d2264 (change p 224 (some 225)) = d56 p := by
  change (if p 162 then d2234 (change p 224 (some 225)) else d2263 (change p 224 (some 225))) = d56 p
  rw [sub9304, sub9336]
  rfl
theorem sub9338 (p : Pattern) : d2265 (change p 224 (some 225)) = d65 p := by
  change (if p 161 then d2242 (change p 224 (some 225)) else d2264 (change p 224 (some 225))) = d65 p
  rw [sub9315, sub9337]
  rfl
theorem sub9339 (p : Pattern) : d2266 (change p 224 (some 225)) = d83 p := by
  change (if p 163 then d12 (change p 224 (some 225)) else d2258 (change p 224 (some 225))) = d83 p
  rw [sub9236, sub9331]
  rfl
theorem sub9340 (p : Pattern) : d2267 (change p 224 (some 225)) = d84 p := by
  change (if p 162 then d12 (change p 224 (some 225)) else d2266 (change p 224 (some 225))) = d84 p
  rw [sub9236, sub9339]
  rfl
theorem sub9341 (p : Pattern) : d2268 (change p 224 (some 225)) = d85 p := by
  change (if p 161 then d12 (change p 224 (some 225)) else d2267 (change p 224 (some 225))) = d85 p
  rw [sub9236, sub9340]
  rfl
theorem sub9342 (p : Pattern) : d2269 (change p 224 (some 225)) = d86 p := by
  change (if p 160 then d2268 (change p 224 (some 225)) else d2265 (change p 224 (some 225))) = d86 p
  rw [sub9341, sub9338]
  rfl
theorem sub9343 (p : Pattern) : d2270 (change p 224 (some 225)) = d87 p := by
  change (if p 141 then d2269 (change p 224 (some 225)) else d2262 (change p 224 (some 225))) = d87 p
  rw [sub9342, sub9335]
  rfl
theorem sub9344 (p : Pattern) : d2271 (change p 224 (some 225)) = d88 p := by
  change (if p 138 then d2270 (change p 224 (some 225)) else d2255 (change p 224 (some 225))) = d88 p
  rw [sub9343, sub9328]
  rfl
theorem sub9345 (p : Pattern) : d2272 (change p 224 (some 225)) = d16 p := by
  change (if p 163 then d2201 (change p 224 (some 225)) else d2195 (change p 224 (some 225))) = d16 p
  rw [sub9259, sub9250]
  simp only [ite_self]
theorem sub9346 (p : Pattern) : d2273 (change p 224 (some 225)) = d22 p := by
  change (if p 162 then d2202 (change p 224 (some 225)) else d2272 (change p 224 (some 225))) = d22 p
  rw [sub9260, sub9345]
  rfl
theorem sub9347 (p : Pattern) : d2274 (change p 224 (some 225)) = d29 p := by
  change (if p 161 then d2207 (change p 224 (some 225)) else d2273 (change p 224 (some 225))) = d29 p
  rw [sub9268, sub9346]
  rfl
theorem sub9348 (p : Pattern) : d2275 (change p 224 (some 225)) = d82 p := by
  change (if p 160 then d2261 (change p 224 (some 225)) else d2274 (change p 224 (some 225))) = d82 p
  rw [sub9334, sub9347]
  rfl
theorem sub9349 (p : Pattern) : d2276 (change p 224 (some 225)) = d87 p := by
  change (if p 141 then d2269 (change p 224 (some 225)) else d2275 (change p 224 (some 225))) = d87 p
  rw [sub9342, sub9348]
  rfl
theorem sub9350 (p : Pattern) : d2277 (change p 224 (some 225)) = d89 p := by
  change (if p 163 then d2240 (change p 224 (some 225)) else d2205 (change p 224 (some 225))) = d89 p
  rw [sub9313, sub9266]
  rfl
theorem sub9351 (p : Pattern) : d2278 (change p 224 (some 225)) = d90 p := by
  change (if p 162 then d2241 (change p 224 (some 225)) else d2277 (change p 224 (some 225))) = d90 p
  rw [sub9314, sub9350]
  rfl
theorem sub9352 (p : Pattern) : d2279 (change p 224 (some 225)) = d91 p := by
  change (if p 162 then d12 (change p 224 (some 225)) else d2241 (change p 224 (some 225))) = d91 p
  rw [sub9236, sub9314]
  rfl
theorem sub9353 (p : Pattern) : d2280 (change p 224 (some 225)) = d92 p := by
  change (if p 161 then d2279 (change p 224 (some 225)) else d2278 (change p 224 (some 225))) = d92 p
  rw [sub9352, sub9351]
  rfl
theorem sub9354 (p : Pattern) : d2281 (change p 224 (some 225)) = d93 p := by
  change (if p 161 then d12 (change p 224 (some 225)) else d2279 (change p 224 (some 225))) = d93 p
  rw [sub9236, sub9352]
  rfl
theorem sub9355 (p : Pattern) : d2282 (change p 224 (some 225)) = d94 p := by
  change (if p 160 then d2281 (change p 224 (some 225)) else d2280 (change p 224 (some 225))) = d94 p
  rw [sub9354, sub9353]
  rfl
theorem sub9356 (p : Pattern) : d2283 (change p 224 (some 225)) = d95 p := by
  change (if p 160 then d12 (change p 224 (some 225)) else d2281 (change p 224 (some 225))) = d95 p
  rw [sub9236, sub9354]
  rfl
theorem sub9357 (p : Pattern) : d2284 (change p 224 (some 225)) = d96 p := by
  change (if p 141 then d2283 (change p 224 (some 225)) else d2282 (change p 224 (some 225))) = d96 p
  rw [sub9356, sub9355]
  rfl
theorem sub9358 (p : Pattern) : d2285 (change p 224 (some 225)) = d97 p := by
  change (if p 138 then d2284 (change p 224 (some 225)) else d2276 (change p 224 (some 225))) = d97 p
  rw [sub9357, sub9349]
  rfl
theorem sub9359 (p : Pattern) : d2286 (change p 224 (some 225)) = d98 p := by
  change (if p 116 then d2285 (change p 224 (some 225)) else d2271 (change p 224 (some 225))) = d98 p
  rw [sub9358, sub9344]
  rfl
end NetHack.Sokoban22Refined85
