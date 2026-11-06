import NetHack.Soko22Hazard87.OldNodes017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldNode7304 (p : Pattern) : NetHack.Sokoban22Refined85.d7304 p = d370996 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d6 p else NetHack.Sokoban22Refined85.d2 p) = d370996 p
  rw [oldNode6, oldNode2]
  rfl
theorem oldNode7305 (p : Pattern) : NetHack.Sokoban22Refined85.d7305 p = d370997 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d6 p else NetHack.Sokoban22Refined85.d7304 p) = d370997 p
  rw [oldNode6, oldNode7304]
  rfl
theorem oldNode7306 (p : Pattern) : NetHack.Sokoban22Refined85.d7306 p = d370998 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7305 p else NetHack.Sokoban22Refined85.d2 p) = d370998 p
  rw [oldNode7305, oldNode2]
  rfl
theorem oldNode7307 (p : Pattern) : NetHack.Sokoban22Refined85.d7307 p = d370999 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d4 p else NetHack.Sokoban22Refined85.d2 p) = d370999 p
  rw [oldNode4, oldNode2]
  rfl
theorem oldNode7308 (p : Pattern) : NetHack.Sokoban22Refined85.d7308 p = d371000 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d4 p else NetHack.Sokoban22Refined85.d7307 p) = d371000 p
  rw [oldNode4, oldNode7307]
  rfl
theorem oldNode7309 (p : Pattern) : NetHack.Sokoban22Refined85.d7309 p = d371001 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7308 p) = d371001 p
  rw [oldNode12, oldNode7308]
  rfl
theorem oldNode7310 (p : Pattern) : NetHack.Sokoban22Refined85.d7310 p = d371002 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7309 p else NetHack.Sokoban22Refined85.d7306 p) = d371002 p
  rw [oldNode7309, oldNode7306]
  rfl
theorem oldNode7311 (p : Pattern) : NetHack.Sokoban22Refined85.d7311 p = d371003 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7310 p else NetHack.Sokoban22Refined85.d7251 p) = d371003 p
  rw [oldNode7310, oldNode7251]
  rfl
theorem oldNode7312 (p : Pattern) : NetHack.Sokoban22Refined85.d7312 p = d371004 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7267 p else NetHack.Sokoban22Refined85.d7258 p) = d371004 p
  rw [oldNode7267, oldNode7258]
  rfl
theorem oldNode7313 (p : Pattern) : NetHack.Sokoban22Refined85.d7313 p = d371005 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7312 p else NetHack.Sokoban22Refined85.d7311 p) = d371005 p
  rw [oldNode7312, oldNode7311]
  rfl
theorem oldNode7314 (p : Pattern) : NetHack.Sokoban22Refined85.d7314 p = d371006 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7281 p) = d371006 p
  rw [oldNode12, oldNode7281]
  rfl
theorem oldNode7315 (p : Pattern) : NetHack.Sokoban22Refined85.d7315 p = d371007 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7314 p else NetHack.Sokoban22Refined85.d10 p) = d371007 p
  rw [oldNode7314, oldNode10]
  rfl
theorem oldNode7316 (p : Pattern) : NetHack.Sokoban22Refined85.d7316 p = d371008 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7314 p) = d371008 p
  rw [oldNode12, oldNode7314]
  rfl
theorem oldNode7317 (p : Pattern) : NetHack.Sokoban22Refined85.d7317 p = d371009 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7316 p else NetHack.Sokoban22Refined85.d7315 p) = d371009 p
  rw [oldNode7316, oldNode7315]
  rfl
theorem oldNode7318 (p : Pattern) : NetHack.Sokoban22Refined85.d7318 p = d371010 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7317 p else NetHack.Sokoban22Refined85.d7258 p) = d371010 p
  rw [oldNode7317, oldNode7258]
  rfl
theorem oldNode7319 (p : Pattern) : NetHack.Sokoban22Refined85.d7319 p = d371011 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7287 p else NetHack.Sokoban22Refined85.d11 p) = d371011 p
  rw [oldNode7287, oldNode11]
  rfl
theorem oldNode7320 (p : Pattern) : NetHack.Sokoban22Refined85.d7320 p = d371012 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7288 p else NetHack.Sokoban22Refined85.d7319 p) = d371012 p
  rw [oldNode7288, oldNode7319]
  rfl
theorem oldNode7321 (p : Pattern) : NetHack.Sokoban22Refined85.d7321 p = d371013 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7320 p) = d371013 p
  rw [oldNode12, oldNode7320]
  rfl
theorem oldNode7322 (p : Pattern) : NetHack.Sokoban22Refined85.d7322 p = d371014 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7321 p else NetHack.Sokoban22Refined85.d7318 p) = d371014 p
  rw [oldNode7321, oldNode7318]
  rfl
theorem oldNode7323 (p : Pattern) : NetHack.Sokoban22Refined85.d7323 p = d371015 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7322 p else NetHack.Sokoban22Refined85.d7313 p) = d371015 p
  rw [oldNode7322, oldNode7313]
  rfl
theorem oldNode7324 (p : Pattern) : NetHack.Sokoban22Refined85.d7324 p = d371016 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7277 p else NetHack.Sokoban22Refined85.d2 p) = d371016 p
  rw [oldNode7277, oldNode2]
  rfl
theorem oldNode7325 (p : Pattern) : NetHack.Sokoban22Refined85.d7325 p = d371017 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7324 p) = d371017 p
  rw [oldNode12, oldNode7324]
  rfl
theorem oldNode7326 (p : Pattern) : NetHack.Sokoban22Refined85.d7326 p = d371018 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7325 p else NetHack.Sokoban22Refined85.d7284 p) = d371018 p
  rw [oldNode7325, oldNode7284]
  rfl
theorem oldNode7327 (p : Pattern) : NetHack.Sokoban22Refined85.d7327 p = d371019 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7299 p else NetHack.Sokoban22Refined85.d7294 p) = d371019 p
  rw [oldNode7299, oldNode7294]
  rfl
theorem oldNode7328 (p : Pattern) : NetHack.Sokoban22Refined85.d7328 p = d371020 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7327 p else NetHack.Sokoban22Refined85.d7326 p) = d371020 p
  rw [oldNode7327, oldNode7326]
  rfl
theorem oldNode7329 (p : Pattern) : NetHack.Sokoban22Refined85.d7329 p = d371021 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7315 p) = d371021 p
  rw [oldNode12, oldNode7315]
  rfl
theorem oldNode7330 (p : Pattern) : NetHack.Sokoban22Refined85.d7330 p = d371022 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7329 p else NetHack.Sokoban22Refined85.d7294 p) = d371022 p
  rw [oldNode7329, oldNode7294]
  rfl
theorem oldNode7331 (p : Pattern) : NetHack.Sokoban22Refined85.d7331 p = d371023 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7319 p) = d371023 p
  rw [oldNode12, oldNode7319]
  rfl
theorem oldNode7332 (p : Pattern) : NetHack.Sokoban22Refined85.d7332 p = d371024 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7331 p) = d371024 p
  rw [oldNode12, oldNode7331]
  rfl
theorem oldNode7333 (p : Pattern) : NetHack.Sokoban22Refined85.d7333 p = d371025 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7332 p else NetHack.Sokoban22Refined85.d7330 p) = d371025 p
  rw [oldNode7332, oldNode7330]
  rfl
theorem oldNode7334 (p : Pattern) : NetHack.Sokoban22Refined85.d7334 p = d371026 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7333 p else NetHack.Sokoban22Refined85.d7328 p) = d371026 p
  rw [oldNode7333, oldNode7328]
  rfl
theorem oldNode7335 (p : Pattern) : NetHack.Sokoban22Refined85.d7335 p = d371027 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7334 p else NetHack.Sokoban22Refined85.d7323 p) = d371027 p
  rw [oldNode7334, oldNode7323]
  rfl
theorem oldNode7336 (p : Pattern) : NetHack.Sokoban22Refined85.d7336 p = d371028 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7335 p else NetHack.Sokoban22Refined85.d7303 p) = d371028 p
  rw [oldNode7335, oldNode7303]
  rfl
theorem oldNode7337 (p : Pattern) : NetHack.Sokoban22Refined85.d7337 p = d371029 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7255 p else NetHack.Sokoban22Refined85.d7271 p) = d371029 p
  rw [oldNode7255, oldNode7271]
  rfl
theorem oldNode7338 (p : Pattern) : NetHack.Sokoban22Refined85.d7338 p = d371030 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7337 p else NetHack.Sokoban22Refined85.d0 p) = d371030 p
  rw [oldNode7337, oldNode0]
  rfl
theorem oldNode7339 (p : Pattern) : NetHack.Sokoban22Refined85.d7339 p = d371031 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7246 p) = d371031 p
  rw [oldNode12, oldNode7246]
  rfl
theorem oldNode7340 (p : Pattern) : NetHack.Sokoban22Refined85.d7340 p = d371032 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7339 p else NetHack.Sokoban22Refined85.d7338 p) = d371032 p
  rw [oldNode7339, oldNode7338]
  rfl
theorem oldNode7341 (p : Pattern) : NetHack.Sokoban22Refined85.d7341 p = d371033 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7252 p else NetHack.Sokoban22Refined85.d7271 p) = d371033 p
  rw [oldNode7252, oldNode7271]
  rfl
theorem oldNode7342 (p : Pattern) : NetHack.Sokoban22Refined85.d7342 p = d371034 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7341 p) = d371034 p
  rw [oldNode12, oldNode7341]
  rfl
theorem oldNode7343 (p : Pattern) : NetHack.Sokoban22Refined85.d7343 p = d371035 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7342 p else NetHack.Sokoban22Refined85.d7274 p) = d371035 p
  rw [oldNode7342, oldNode7274]
  rfl
theorem oldNode7344 (p : Pattern) : NetHack.Sokoban22Refined85.d7344 p = d371036 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7343 p else NetHack.Sokoban22Refined85.d7340 p) = d371036 p
  rw [oldNode7343, oldNode7340]
  rfl
theorem oldNode7345 (p : Pattern) : NetHack.Sokoban22Refined85.d7345 p = d371037 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7273 p) = d371037 p
  rw [oldNode12, oldNode7273]
  rfl
theorem oldNode7346 (p : Pattern) : NetHack.Sokoban22Refined85.d7346 p = d371038 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7345 p else NetHack.Sokoban22Refined85.d7274 p) = d371038 p
  rw [oldNode7345, oldNode7274]
  rfl
theorem oldNode7347 (p : Pattern) : NetHack.Sokoban22Refined85.d7347 p = d371039 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7292 p) = d371039 p
  rw [oldNode12, oldNode7292]
  rfl
theorem oldNode7348 (p : Pattern) : NetHack.Sokoban22Refined85.d7348 p = d371040 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7347 p else NetHack.Sokoban22Refined85.d7293 p) = d371040 p
  rw [oldNode7347, oldNode7293]
  rfl
theorem oldNode7349 (p : Pattern) : NetHack.Sokoban22Refined85.d7349 p = d371041 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7348 p else NetHack.Sokoban22Refined85.d7346 p) = d371041 p
  rw [oldNode7348, oldNode7346]
  rfl
theorem oldNode7350 (p : Pattern) : NetHack.Sokoban22Refined85.d7350 p = d371042 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7349 p else NetHack.Sokoban22Refined85.d7344 p) = d371042 p
  rw [oldNode7349, oldNode7344]
  rfl
theorem oldNode7351 (p : Pattern) : NetHack.Sokoban22Refined85.d7351 p = d371043 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7262 p) = d371043 p
  rw [oldNode12, oldNode7262]
  rfl
theorem oldNode7352 (p : Pattern) : NetHack.Sokoban22Refined85.d7352 p = d371044 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7351 p else NetHack.Sokoban22Refined85.d7263 p) = d371044 p
  rw [oldNode7351, oldNode7263]
  rfl
theorem oldNode7353 (p : Pattern) : NetHack.Sokoban22Refined85.d7353 p = d371045 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7352 p) = d371045 p
  rw [oldNode12, oldNode7352]
  rfl
theorem oldNode7354 (p : Pattern) : NetHack.Sokoban22Refined85.d7354 p = d371046 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7353 p else NetHack.Sokoban22Refined85.d7349 p) = d371046 p
  rw [oldNode7353, oldNode7349]
  rfl
theorem oldNode7355 (p : Pattern) : NetHack.Sokoban22Refined85.d7355 p = d371047 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7354 p else NetHack.Sokoban22Refined85.d7350 p) = d371047 p
  rw [oldNode7354, oldNode7350]
  rfl
theorem oldNode7356 (p : Pattern) : NetHack.Sokoban22Refined85.d7356 p = d371048 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7278 p else NetHack.Sokoban22Refined85.d7324 p) = d371048 p
  rw [oldNode7278, oldNode7324]
  rfl
theorem oldNode7357 (p : Pattern) : NetHack.Sokoban22Refined85.d7357 p = d371049 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7282 p else NetHack.Sokoban22Refined85.d6 p) = d371049 p
  rw [oldNode7282, oldNode6]
  rfl
theorem oldNode7358 (p : Pattern) : NetHack.Sokoban22Refined85.d7358 p = d371050 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7283 p else NetHack.Sokoban22Refined85.d7357 p) = d371050 p
  rw [oldNode7283, oldNode7357]
  rfl
theorem oldNode7359 (p : Pattern) : NetHack.Sokoban22Refined85.d7359 p = d371051 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7358 p else NetHack.Sokoban22Refined85.d7356 p) = d371051 p
  rw [oldNode7358, oldNode7356]
  rfl
theorem oldNode7360 (p : Pattern) : NetHack.Sokoban22Refined85.d7360 p = d371052 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7321 p else NetHack.Sokoban22Refined85.d7359 p) = d371052 p
  rw [oldNode7321, oldNode7359]
  rfl
theorem oldNode7361 (p : Pattern) : NetHack.Sokoban22Refined85.d7361 p = d371053 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7360 p) = d371053 p
  rw [oldNode12, oldNode7360]
  rfl
theorem oldNode7362 (p : Pattern) : NetHack.Sokoban22Refined85.d7362 p = d371054 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7361 p else NetHack.Sokoban22Refined85.d7355 p) = d371054 p
  rw [oldNode7361, oldNode7355]
  rfl
theorem oldNode7363 (p : Pattern) : NetHack.Sokoban22Refined85.d7363 p = d371055 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7356 p else NetHack.Sokoban22Refined85.d7343 p) = d371055 p
  rw [oldNode7356, oldNode7343]
  rfl
theorem oldNode7364 (p : Pattern) : NetHack.Sokoban22Refined85.d7364 p = d371056 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7352 p else NetHack.Sokoban22Refined85.d7348 p) = d371056 p
  rw [oldNode7352, oldNode7348]
  rfl
theorem oldNode7365 (p : Pattern) : NetHack.Sokoban22Refined85.d7365 p = d371057 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7364 p else NetHack.Sokoban22Refined85.d7363 p) = d371057 p
  rw [oldNode7364, oldNode7363]
  rfl
theorem oldNode7366 (p : Pattern) : NetHack.Sokoban22Refined85.d7366 p = d371058 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7317 p else NetHack.Sokoban22Refined85.d7348 p) = d371058 p
  rw [oldNode7317, oldNode7348]
  rfl
theorem oldNode7367 (p : Pattern) : NetHack.Sokoban22Refined85.d7367 p = d371059 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7321 p else NetHack.Sokoban22Refined85.d7366 p) = d371059 p
  rw [oldNode7321, oldNode7366]
  rfl
theorem oldNode7368 (p : Pattern) : NetHack.Sokoban22Refined85.d7368 p = d371060 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7367 p else NetHack.Sokoban22Refined85.d7365 p) = d371060 p
  rw [oldNode7367, oldNode7365]
  rfl
theorem oldNode7369 (p : Pattern) : NetHack.Sokoban22Refined85.d7369 p = d371061 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7358 p) = d371061 p
  rw [oldNode12, oldNode7358]
  rfl
theorem oldNode7370 (p : Pattern) : NetHack.Sokoban22Refined85.d7370 p = d371062 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7369 p) = d371062 p
  rw [oldNode12, oldNode7369]
  rfl
theorem oldNode7371 (p : Pattern) : NetHack.Sokoban22Refined85.d7371 p = d371063 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7370 p) = d371063 p
  rw [oldNode12, oldNode7370]
  rfl
theorem oldNode7372 (p : Pattern) : NetHack.Sokoban22Refined85.d7372 p = d371064 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7371 p else NetHack.Sokoban22Refined85.d7368 p) = d371064 p
  rw [oldNode7371, oldNode7368]
  rfl
theorem oldNode7373 (p : Pattern) : NetHack.Sokoban22Refined85.d7373 p = d371065 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7372 p else NetHack.Sokoban22Refined85.d7362 p) = d371065 p
  rw [oldNode7372, oldNode7362]
  rfl
theorem oldNode7374 (p : Pattern) : NetHack.Sokoban22Refined85.d7374 p = d371066 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d7373 p else NetHack.Sokoban22Refined85.d7336 p) = d371066 p
  rw [oldNode7373, oldNode7336]
  rfl
theorem oldNode7375 (p : Pattern) : NetHack.Sokoban22Refined85.d7375 p = d371067 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7320 p else NetHack.Sokoban22Refined85.d7352 p) = d371067 p
  rw [oldNode7320, oldNode7352]
  rfl
theorem oldNode7376 (p : Pattern) : NetHack.Sokoban22Refined85.d7376 p = d371068 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7321 p else NetHack.Sokoban22Refined85.d7375 p) = d371068 p
  rw [oldNode7321, oldNode7375]
  rfl
theorem oldNode7377 (p : Pattern) : NetHack.Sokoban22Refined85.d7377 p = d371069 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7321 p) = d371069 p
  rw [oldNode12, oldNode7321]
  rfl
theorem oldNode7378 (p : Pattern) : NetHack.Sokoban22Refined85.d7378 p = d371070 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7377 p else NetHack.Sokoban22Refined85.d7376 p) = d371070 p
  rw [oldNode7377, oldNode7376]
  rfl
theorem oldNode7379 (p : Pattern) : NetHack.Sokoban22Refined85.d7379 p = d371071 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7377 p) = d371071 p
  rw [oldNode12, oldNode7377]
  rfl
theorem oldNode7380 (p : Pattern) : NetHack.Sokoban22Refined85.d7380 p = d371072 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7379 p else NetHack.Sokoban22Refined85.d7378 p) = d371072 p
  rw [oldNode7379, oldNode7378]
  rfl
theorem oldNode7381 (p : Pattern) : NetHack.Sokoban22Refined85.d7381 p = d371073 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7379 p) = d371073 p
  rw [oldNode12, oldNode7379]
  rfl
theorem oldNode7382 (p : Pattern) : NetHack.Sokoban22Refined85.d7382 p = d371074 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7381 p else NetHack.Sokoban22Refined85.d7380 p) = d371074 p
  rw [oldNode7381, oldNode7380]
  rfl
theorem oldNode7383 (p : Pattern) : NetHack.Sokoban22Refined85.d7383 p = d371075 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d7382 p else NetHack.Sokoban22Refined85.d7373 p) = d371075 p
  rw [oldNode7382, oldNode7373]
  rfl
theorem oldNode7384 (p : Pattern) : NetHack.Sokoban22Refined85.d7384 p = d371076 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d7383 p else NetHack.Sokoban22Refined85.d7374 p) = d371076 p
  rw [oldNode7383, oldNode7374]
  rfl
theorem oldNode7385 (p : Pattern) : NetHack.Sokoban22Refined85.d7385 p = d371077 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7373 p) = d371077 p
  rw [oldNode12, oldNode7373]
  rfl
theorem oldNode7386 (p : Pattern) : NetHack.Sokoban22Refined85.d7386 p = d371078 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d7385 p else NetHack.Sokoban22Refined85.d7374 p) = d371078 p
  rw [oldNode7385, oldNode7374]
  rfl
theorem oldNode7387 (p : Pattern) : NetHack.Sokoban22Refined85.d7387 p = d371079 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d7386 p else NetHack.Sokoban22Refined85.d7384 p) = d371079 p
  rw [oldNode7386, oldNode7384]
  rfl
theorem oldNode7388 (p : Pattern) : NetHack.Sokoban22Refined85.d7388 p = d371080 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d5 p else NetHack.Sokoban22Refined85.d1 p) = d371080 p
  rw [oldNode5, oldNode1]
  rfl
theorem oldNode7389 (p : Pattern) : NetHack.Sokoban22Refined85.d7389 p = d371081 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d5 p else NetHack.Sokoban22Refined85.d7388 p) = d371081 p
  rw [oldNode5, oldNode7388]
  rfl
theorem oldNode7390 (p : Pattern) : NetHack.Sokoban22Refined85.d7390 p = d371082 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7389 p else NetHack.Sokoban22Refined85.d1 p) = d371082 p
  rw [oldNode7389, oldNode1]
  rfl
theorem oldNode7391 (p : Pattern) : NetHack.Sokoban22Refined85.d7391 p = d371083 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3 p else NetHack.Sokoban22Refined85.d1 p) = d371083 p
  rw [oldNode3, oldNode1]
  rfl
theorem oldNode7392 (p : Pattern) : NetHack.Sokoban22Refined85.d7392 p = d371084 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d3 p else NetHack.Sokoban22Refined85.d7391 p) = d371084 p
  rw [oldNode3, oldNode7391]
  rfl
theorem oldNode7393 (p : Pattern) : NetHack.Sokoban22Refined85.d7393 p = d371085 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7392 p) = d371085 p
  rw [oldNode12, oldNode7392]
  rfl
theorem oldNode7394 (p : Pattern) : NetHack.Sokoban22Refined85.d7394 p = d371086 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7393 p else NetHack.Sokoban22Refined85.d7390 p) = d371086 p
  rw [oldNode7393, oldNode7390]
  rfl
theorem oldNode7395 (p : Pattern) : NetHack.Sokoban22Refined85.d7395 p = d371087 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d9 p else NetHack.Sokoban22Refined85.d5 p) = d371087 p
  rw [oldNode9, oldNode5]
  rfl
theorem oldNode7396 (p : Pattern) : NetHack.Sokoban22Refined85.d7396 p = d371088 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d9 p else NetHack.Sokoban22Refined85.d7395 p) = d371088 p
  rw [oldNode9, oldNode7395]
  rfl
theorem oldNode7397 (p : Pattern) : NetHack.Sokoban22Refined85.d7397 p = d371089 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7396 p else NetHack.Sokoban22Refined85.d5 p) = d371089 p
  rw [oldNode7396, oldNode5]
  rfl
theorem oldNode7398 (p : Pattern) : NetHack.Sokoban22Refined85.d7398 p = d371090 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d7 p else NetHack.Sokoban22Refined85.d5 p) = d371090 p
  rw [oldNode7, oldNode5]
  rfl
theorem oldNode7399 (p : Pattern) : NetHack.Sokoban22Refined85.d7399 p = d371091 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7 p else NetHack.Sokoban22Refined85.d7398 p) = d371091 p
  rw [oldNode7, oldNode7398]
  rfl
theorem oldNode7400 (p : Pattern) : NetHack.Sokoban22Refined85.d7400 p = d371092 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7399 p) = d371092 p
  rw [oldNode12, oldNode7399]
  rfl
theorem oldNode7401 (p : Pattern) : NetHack.Sokoban22Refined85.d7401 p = d371093 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7400 p else NetHack.Sokoban22Refined85.d7397 p) = d371093 p
  rw [oldNode7400, oldNode7397]
  rfl
theorem oldNode7402 (p : Pattern) : NetHack.Sokoban22Refined85.d7402 p = d371094 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7401 p else NetHack.Sokoban22Refined85.d7394 p) = d371094 p
  rw [oldNode7401, oldNode7394]
  rfl
theorem oldNode7403 (p : Pattern) : NetHack.Sokoban22Refined85.d7403 p = d371095 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7402 p else NetHack.Sokoban22Refined85.d7394 p) = d371095 p
  rw [oldNode7402, oldNode7394]
  rfl
theorem oldNode7404 (p : Pattern) : NetHack.Sokoban22Refined85.d7404 p = d371096 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7317 p) = d371096 p
  rw [oldNode12, oldNode7317]
  rfl
theorem oldNode7405 (p : Pattern) : NetHack.Sokoban22Refined85.d7405 p = d371097 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7404 p else NetHack.Sokoban22Refined85.d7402 p) = d371097 p
  rw [oldNode7404, oldNode7402]
  rfl
theorem oldNode7406 (p : Pattern) : NetHack.Sokoban22Refined85.d7406 p = d371098 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7405 p else NetHack.Sokoban22Refined85.d7403 p) = d371098 p
  rw [oldNode7405, oldNode7403]
  rfl
theorem oldNode7407 (p : Pattern) : NetHack.Sokoban22Refined85.d7407 p = d371099 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d7 p else NetHack.Sokoban22Refined85.d1 p) = d371099 p
  rw [oldNode7, oldNode1]
  rfl
theorem oldNode7408 (p : Pattern) : NetHack.Sokoban22Refined85.d7408 p = d371100 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d10 p else NetHack.Sokoban22Refined85.d5 p) = d371100 p
  rw [oldNode10, oldNode5]
  rfl
theorem oldNode7409 (p : Pattern) : NetHack.Sokoban22Refined85.d7409 p = d371101 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7408 p else NetHack.Sokoban22Refined85.d7407 p) = d371101 p
  rw [oldNode7408, oldNode7407]
  rfl
theorem oldNode7410 (p : Pattern) : NetHack.Sokoban22Refined85.d7410 p = d371102 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7409 p else NetHack.Sokoban22Refined85.d1 p) = d371102 p
  rw [oldNode7409, oldNode1]
  rfl
theorem oldNode7411 (p : Pattern) : NetHack.Sokoban22Refined85.d7411 p = d371103 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d9 p else NetHack.Sokoban22Refined85.d3 p) = d371103 p
  rw [oldNode9, oldNode3]
  rfl
theorem oldNode7412 (p : Pattern) : NetHack.Sokoban22Refined85.d7412 p = d371104 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7 p) = d371104 p
  rw [oldNode12, oldNode7]
  rfl
theorem oldNode7413 (p : Pattern) : NetHack.Sokoban22Refined85.d7413 p = d371105 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7412 p else NetHack.Sokoban22Refined85.d7411 p) = d371105 p
  rw [oldNode7412, oldNode7411]
  rfl
theorem oldNode7414 (p : Pattern) : NetHack.Sokoban22Refined85.d7414 p = d371106 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7413 p) = d371106 p
  rw [oldNode12, oldNode7413]
  rfl
theorem oldNode7415 (p : Pattern) : NetHack.Sokoban22Refined85.d7415 p = d371107 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7414 p else NetHack.Sokoban22Refined85.d7410 p) = d371107 p
  rw [oldNode7414, oldNode7410]
  rfl
theorem oldNode7416 (p : Pattern) : NetHack.Sokoban22Refined85.d7416 p = d371108 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7286 p else NetHack.Sokoban22Refined85.d7412 p) = d371108 p
  rw [oldNode7286, oldNode7412]
  rfl
theorem oldNode7417 (p : Pattern) : NetHack.Sokoban22Refined85.d7417 p = d371109 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7416 p) = d371109 p
  rw [oldNode12, oldNode7416]
  rfl
theorem oldNode7418 (p : Pattern) : NetHack.Sokoban22Refined85.d7418 p = d371110 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7417 p else NetHack.Sokoban22Refined85.d7410 p) = d371110 p
  rw [oldNode7417, oldNode7410]
  rfl
theorem oldNode7419 (p : Pattern) : NetHack.Sokoban22Refined85.d7419 p = d371111 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7418 p else NetHack.Sokoban22Refined85.d7415 p) = d371111 p
  rw [oldNode7418, oldNode7415]
  rfl
theorem oldNode7420 (p : Pattern) : NetHack.Sokoban22Refined85.d7420 p = d371112 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7410 p) = d371112 p
  rw [oldNode12, oldNode7410]
  rfl
theorem oldNode7421 (p : Pattern) : NetHack.Sokoban22Refined85.d7421 p = d371113 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d11 p else NetHack.Sokoban22Refined85.d5 p) = d371113 p
  rw [oldNode11, oldNode5]
  rfl
theorem oldNode7422 (p : Pattern) : NetHack.Sokoban22Refined85.d7422 p = d371114 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7261 p else NetHack.Sokoban22Refined85.d7421 p) = d371114 p
  rw [oldNode7261, oldNode7421]
  rfl
theorem oldNode7423 (p : Pattern) : NetHack.Sokoban22Refined85.d7423 p = d371115 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7422 p else NetHack.Sokoban22Refined85.d5 p) = d371115 p
  rw [oldNode7422, oldNode5]
  rfl
theorem oldNode7424 (p : Pattern) : NetHack.Sokoban22Refined85.d7424 p = d371116 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7423 p) = d371116 p
  rw [oldNode12, oldNode7423]
  rfl
theorem oldNode7425 (p : Pattern) : NetHack.Sokoban22Refined85.d7425 p = d371117 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7424 p else NetHack.Sokoban22Refined85.d7420 p) = d371117 p
  rw [oldNode7424, oldNode7420]
  rfl
theorem oldNode7426 (p : Pattern) : NetHack.Sokoban22Refined85.d7426 p = d371118 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7425 p else NetHack.Sokoban22Refined85.d7419 p) = d371118 p
  rw [oldNode7425, oldNode7419]
  rfl
theorem oldNode7427 (p : Pattern) : NetHack.Sokoban22Refined85.d7427 p = d371119 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7329 p) = d371119 p
  rw [oldNode12, oldNode7329]
  rfl
theorem oldNode7428 (p : Pattern) : NetHack.Sokoban22Refined85.d7428 p = d371120 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7427 p else NetHack.Sokoban22Refined85.d7425 p) = d371120 p
  rw [oldNode7427, oldNode7425]
  rfl
theorem oldNode7429 (p : Pattern) : NetHack.Sokoban22Refined85.d7429 p = d371121 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7428 p else NetHack.Sokoban22Refined85.d7426 p) = d371121 p
  rw [oldNode7428, oldNode7426]
  rfl
theorem oldNode7430 (p : Pattern) : NetHack.Sokoban22Refined85.d7430 p = d371122 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7429 p else NetHack.Sokoban22Refined85.d7406 p) = d371122 p
  rw [oldNode7429, oldNode7406]
  rfl
theorem oldNode7431 (p : Pattern) : NetHack.Sokoban22Refined85.d7431 p = d371123 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d7 p else NetHack.Sokoban22Refined85.d3 p) = d371123 p
  rw [oldNode7, oldNode3]
  rfl
theorem oldNode7432 (p : Pattern) : NetHack.Sokoban22Refined85.d7432 p = d371124 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7 p else NetHack.Sokoban22Refined85.d7431 p) = d371124 p
  rw [oldNode7, oldNode7431]
  rfl
theorem oldNode7433 (p : Pattern) : NetHack.Sokoban22Refined85.d7433 p = d371125 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7432 p else NetHack.Sokoban22Refined85.d3 p) = d371125 p
  rw [oldNode7432, oldNode3]
  rfl
theorem oldNode7434 (p : Pattern) : NetHack.Sokoban22Refined85.d7434 p = d371126 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d5 p else NetHack.Sokoban22Refined85.d3 p) = d371126 p
  rw [oldNode5, oldNode3]
  rfl
theorem oldNode7435 (p : Pattern) : NetHack.Sokoban22Refined85.d7435 p = d371127 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d5 p else NetHack.Sokoban22Refined85.d7434 p) = d371127 p
  rw [oldNode5, oldNode7434]
  rfl
theorem oldNode7436 (p : Pattern) : NetHack.Sokoban22Refined85.d7436 p = d371128 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7435 p) = d371128 p
  rw [oldNode12, oldNode7435]
  rfl
theorem oldNode7437 (p : Pattern) : NetHack.Sokoban22Refined85.d7437 p = d371129 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7436 p else NetHack.Sokoban22Refined85.d7433 p) = d371129 p
  rw [oldNode7436, oldNode7433]
  rfl
theorem oldNode7438 (p : Pattern) : NetHack.Sokoban22Refined85.d7438 p = d371130 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7437 p else NetHack.Sokoban22Refined85.d7394 p) = d371130 p
  rw [oldNode7437, oldNode7394]
  rfl
theorem oldNode7439 (p : Pattern) : NetHack.Sokoban22Refined85.d7439 p = d371131 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7317 p else NetHack.Sokoban22Refined85.d7401 p) = d371131 p
  rw [oldNode7317, oldNode7401]
  rfl
theorem oldNode7440 (p : Pattern) : NetHack.Sokoban22Refined85.d7440 p = d371132 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7439 p else NetHack.Sokoban22Refined85.d7438 p) = d371132 p
  rw [oldNode7439, oldNode7438]
  rfl
theorem oldNode7441 (p : Pattern) : NetHack.Sokoban22Refined85.d7441 p = d371133 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7320 p else NetHack.Sokoban22Refined85.d7401 p) = d371133 p
  rw [oldNode7320, oldNode7401]
  rfl
theorem oldNode7442 (p : Pattern) : NetHack.Sokoban22Refined85.d7442 p = d371134 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7441 p) = d371134 p
  rw [oldNode12, oldNode7441]
  rfl
theorem oldNode7443 (p : Pattern) : NetHack.Sokoban22Refined85.d7443 p = d371135 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7442 p else NetHack.Sokoban22Refined85.d7440 p) = d371135 p
  rw [oldNode7442, oldNode7440]
  rfl
theorem oldNode7444 (p : Pattern) : NetHack.Sokoban22Refined85.d7444 p = d371136 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7413 p else NetHack.Sokoban22Refined85.d3 p) = d371136 p
  rw [oldNode7413, oldNode3]
  rfl
theorem oldNode7445 (p : Pattern) : NetHack.Sokoban22Refined85.d7445 p = d371137 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7444 p) = d371137 p
  rw [oldNode12, oldNode7444]
  rfl
theorem oldNode7446 (p : Pattern) : NetHack.Sokoban22Refined85.d7446 p = d371138 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7445 p else NetHack.Sokoban22Refined85.d7418 p) = d371138 p
  rw [oldNode7445, oldNode7418]
  rfl
theorem oldNode7447 (p : Pattern) : NetHack.Sokoban22Refined85.d7447 p = d371139 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7329 p else NetHack.Sokoban22Refined85.d7424 p) = d371139 p
  rw [oldNode7329, oldNode7424]
  rfl
theorem oldNode7448 (p : Pattern) : NetHack.Sokoban22Refined85.d7448 p = d371140 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7447 p else NetHack.Sokoban22Refined85.d7446 p) = d371140 p
  rw [oldNode7447, oldNode7446]
  rfl
theorem oldNode7449 (p : Pattern) : NetHack.Sokoban22Refined85.d7449 p = d371141 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7331 p else NetHack.Sokoban22Refined85.d7424 p) = d371141 p
  rw [oldNode7331, oldNode7424]
  rfl
theorem oldNode7450 (p : Pattern) : NetHack.Sokoban22Refined85.d7450 p = d371142 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7449 p) = d371142 p
  rw [oldNode12, oldNode7449]
  rfl
theorem oldNode7451 (p : Pattern) : NetHack.Sokoban22Refined85.d7451 p = d371143 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7450 p else NetHack.Sokoban22Refined85.d7448 p) = d371143 p
  rw [oldNode7450, oldNode7448]
  rfl
theorem oldNode7452 (p : Pattern) : NetHack.Sokoban22Refined85.d7452 p = d371144 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7451 p else NetHack.Sokoban22Refined85.d7443 p) = d371144 p
  rw [oldNode7451, oldNode7443]
  rfl
theorem oldNode7453 (p : Pattern) : NetHack.Sokoban22Refined85.d7453 p = d371145 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7452 p else NetHack.Sokoban22Refined85.d7430 p) = d371145 p
  rw [oldNode7452, oldNode7430]
  rfl
theorem oldNode7454 (p : Pattern) : NetHack.Sokoban22Refined85.d7454 p = d371146 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7398 p else NetHack.Sokoban22Refined85.d7407 p) = d371146 p
  rw [oldNode7398, oldNode7407]
  rfl
theorem oldNode7455 (p : Pattern) : NetHack.Sokoban22Refined85.d7455 p = d371147 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7454 p else NetHack.Sokoban22Refined85.d1 p) = d371147 p
  rw [oldNode7454, oldNode1]
  rfl
theorem oldNode7456 (p : Pattern) : NetHack.Sokoban22Refined85.d7456 p = d371148 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7389 p) = d371148 p
  rw [oldNode12, oldNode7389]
  rfl
theorem oldNode7457 (p : Pattern) : NetHack.Sokoban22Refined85.d7457 p = d371149 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7456 p else NetHack.Sokoban22Refined85.d7455 p) = d371149 p
  rw [oldNode7456, oldNode7455]
  rfl
theorem oldNode7458 (p : Pattern) : NetHack.Sokoban22Refined85.d7458 p = d371150 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7395 p else NetHack.Sokoban22Refined85.d7407 p) = d371150 p
  rw [oldNode7395, oldNode7407]
  rfl
theorem oldNode7459 (p : Pattern) : NetHack.Sokoban22Refined85.d7459 p = d371151 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7458 p) = d371151 p
  rw [oldNode12, oldNode7458]
  rfl
theorem oldNode7460 (p : Pattern) : NetHack.Sokoban22Refined85.d7460 p = d371152 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7459 p else NetHack.Sokoban22Refined85.d7410 p) = d371152 p
  rw [oldNode7459, oldNode7410]
  rfl
theorem oldNode7461 (p : Pattern) : NetHack.Sokoban22Refined85.d7461 p = d371153 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7460 p else NetHack.Sokoban22Refined85.d7457 p) = d371153 p
  rw [oldNode7460, oldNode7457]
  rfl
theorem oldNode7462 (p : Pattern) : NetHack.Sokoban22Refined85.d7462 p = d371154 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7409 p) = d371154 p
  rw [oldNode12, oldNode7409]
  rfl
theorem oldNode7463 (p : Pattern) : NetHack.Sokoban22Refined85.d7463 p = d371155 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7462 p else NetHack.Sokoban22Refined85.d7410 p) = d371155 p
  rw [oldNode7462, oldNode7410]
  rfl
theorem oldNode7464 (p : Pattern) : NetHack.Sokoban22Refined85.d7464 p = d371156 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7422 p) = d371156 p
  rw [oldNode12, oldNode7422]
  rfl
theorem oldNode7465 (p : Pattern) : NetHack.Sokoban22Refined85.d7465 p = d371157 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7464 p else NetHack.Sokoban22Refined85.d7423 p) = d371157 p
  rw [oldNode7464, oldNode7423]
  rfl
theorem oldNode7466 (p : Pattern) : NetHack.Sokoban22Refined85.d7466 p = d371158 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7465 p else NetHack.Sokoban22Refined85.d7463 p) = d371158 p
  rw [oldNode7465, oldNode7463]
  rfl
theorem oldNode7467 (p : Pattern) : NetHack.Sokoban22Refined85.d7467 p = d371159 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7466 p else NetHack.Sokoban22Refined85.d7461 p) = d371159 p
  rw [oldNode7466, oldNode7461]
  rfl
theorem oldNode7468 (p : Pattern) : NetHack.Sokoban22Refined85.d7468 p = d371160 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7404 p else NetHack.Sokoban22Refined85.d7466 p) = d371160 p
  rw [oldNode7404, oldNode7466]
  rfl
theorem oldNode7469 (p : Pattern) : NetHack.Sokoban22Refined85.d7469 p = d371161 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7468 p else NetHack.Sokoban22Refined85.d7467 p) = d371161 p
  rw [oldNode7468, oldNode7467]
  rfl
theorem oldNode7470 (p : Pattern) : NetHack.Sokoban22Refined85.d7470 p = d371162 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7414 p else NetHack.Sokoban22Refined85.d7444 p) = d371162 p
  rw [oldNode7414, oldNode7444]
  rfl
theorem oldNode7471 (p : Pattern) : NetHack.Sokoban22Refined85.d7471 p = d371163 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7416 p else NetHack.Sokoban22Refined85.d7 p) = d371163 p
  rw [oldNode7416, oldNode7]
  rfl
theorem oldNode7472 (p : Pattern) : NetHack.Sokoban22Refined85.d7472 p = d371164 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7417 p else NetHack.Sokoban22Refined85.d7471 p) = d371164 p
  rw [oldNode7417, oldNode7471]
  rfl
theorem oldNode7473 (p : Pattern) : NetHack.Sokoban22Refined85.d7473 p = d371165 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7472 p else NetHack.Sokoban22Refined85.d7470 p) = d371165 p
  rw [oldNode7472, oldNode7470]
  rfl
theorem oldNode7474 (p : Pattern) : NetHack.Sokoban22Refined85.d7474 p = d371166 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7473 p) = d371166 p
  rw [oldNode12, oldNode7473]
  rfl
theorem oldNode7475 (p : Pattern) : NetHack.Sokoban22Refined85.d7475 p = d371167 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7474 p) = d371167 p
  rw [oldNode12, oldNode7474]
  rfl
theorem oldNode7476 (p : Pattern) : NetHack.Sokoban22Refined85.d7476 p = d371168 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7475 p else NetHack.Sokoban22Refined85.d7469 p) = d371168 p
  rw [oldNode7475, oldNode7469]
  rfl
theorem oldNode7477 (p : Pattern) : NetHack.Sokoban22Refined85.d7477 p = d371169 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7470 p else NetHack.Sokoban22Refined85.d7460 p) = d371169 p
  rw [oldNode7470, oldNode7460]
  rfl
theorem oldNode7478 (p : Pattern) : NetHack.Sokoban22Refined85.d7478 p = d371170 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7317 p else NetHack.Sokoban22Refined85.d7465 p) = d371170 p
  rw [oldNode7317, oldNode7465]
  rfl
theorem oldNode7479 (p : Pattern) : NetHack.Sokoban22Refined85.d7479 p = d371171 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7478 p else NetHack.Sokoban22Refined85.d7477 p) = d371171 p
  rw [oldNode7478, oldNode7477]
  rfl
theorem oldNode7480 (p : Pattern) : NetHack.Sokoban22Refined85.d7480 p = d371172 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7320 p else NetHack.Sokoban22Refined85.d7465 p) = d371172 p
  rw [oldNode7320, oldNode7465]
  rfl
theorem oldNode7481 (p : Pattern) : NetHack.Sokoban22Refined85.d7481 p = d371173 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7480 p) = d371173 p
  rw [oldNode12, oldNode7480]
  rfl
theorem oldNode7482 (p : Pattern) : NetHack.Sokoban22Refined85.d7482 p = d371174 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7481 p else NetHack.Sokoban22Refined85.d7479 p) = d371174 p
  rw [oldNode7481, oldNode7479]
  rfl
theorem oldNode7483 (p : Pattern) : NetHack.Sokoban22Refined85.d7483 p = d371175 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7472 p) = d371175 p
  rw [oldNode12, oldNode7472]
  rfl
theorem oldNode7484 (p : Pattern) : NetHack.Sokoban22Refined85.d7484 p = d371176 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7483 p) = d371176 p
  rw [oldNode12, oldNode7483]
  rfl
theorem oldNode7485 (p : Pattern) : NetHack.Sokoban22Refined85.d7485 p = d371177 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7484 p) = d371177 p
  rw [oldNode12, oldNode7484]
  rfl
theorem oldNode7486 (p : Pattern) : NetHack.Sokoban22Refined85.d7486 p = d371178 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7485 p else NetHack.Sokoban22Refined85.d7482 p) = d371178 p
  rw [oldNode7485, oldNode7482]
  rfl
theorem oldNode7487 (p : Pattern) : NetHack.Sokoban22Refined85.d7487 p = d371179 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7486 p else NetHack.Sokoban22Refined85.d7476 p) = d371179 p
  rw [oldNode7486, oldNode7476]
  rfl
theorem oldNode7488 (p : Pattern) : NetHack.Sokoban22Refined85.d7488 p = d371180 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d7487 p else NetHack.Sokoban22Refined85.d7453 p) = d371180 p
  rw [oldNode7487, oldNode7453]
  rfl
theorem oldNode7489 (p : Pattern) : NetHack.Sokoban22Refined85.d7489 p = d371181 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7404 p) = d371181 p
  rw [oldNode12, oldNode7404]
  rfl
theorem oldNode7490 (p : Pattern) : NetHack.Sokoban22Refined85.d7490 p = d371182 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7489 p) = d371182 p
  rw [oldNode12, oldNode7489]
  rfl
theorem oldNode7491 (p : Pattern) : NetHack.Sokoban22Refined85.d7491 p = d371183 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7490 p) = d371183 p
  rw [oldNode12, oldNode7490]
  rfl
theorem oldNode7492 (p : Pattern) : NetHack.Sokoban22Refined85.d7492 p = d371184 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7491 p) = d371184 p
  rw [oldNode12, oldNode7491]
  rfl
theorem oldNode7493 (p : Pattern) : NetHack.Sokoban22Refined85.d7493 p = d371185 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d7492 p else NetHack.Sokoban22Refined85.d7487 p) = d371185 p
  rw [oldNode7492, oldNode7487]
  rfl
theorem oldNode7494 (p : Pattern) : NetHack.Sokoban22Refined85.d7494 p = d371186 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d7493 p else NetHack.Sokoban22Refined85.d7488 p) = d371186 p
  rw [oldNode7493, oldNode7488]
  rfl
theorem oldNode7495 (p : Pattern) : NetHack.Sokoban22Refined85.d7495 p = d371187 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7487 p) = d371187 p
  rw [oldNode12, oldNode7487]
  rfl
theorem oldNode7496 (p : Pattern) : NetHack.Sokoban22Refined85.d7496 p = d371188 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d7495 p else NetHack.Sokoban22Refined85.d7488 p) = d371188 p
  rw [oldNode7495, oldNode7488]
  rfl
theorem oldNode7497 (p : Pattern) : NetHack.Sokoban22Refined85.d7497 p = d371189 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d7496 p else NetHack.Sokoban22Refined85.d7494 p) = d371189 p
  rw [oldNode7496, oldNode7494]
  rfl
theorem oldNode7498 (p : Pattern) : NetHack.Sokoban22Refined85.d7498 p = d371190 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d7497 p else NetHack.Sokoban22Refined85.d7387 p) = d371190 p
  rw [oldNode7497, oldNode7387]
  rfl
theorem oldNode7499 (p : Pattern) : NetHack.Sokoban22Refined85.d7499 p = d371191 p := by
  change (if p 49 then NetHack.Sokoban22Refined85.d7498 p else NetHack.Sokoban22Refined85.d7387 p) = d371191 p
  rw [oldNode7498, oldNode7387]
  rfl
theorem oldNode7500 (p : Pattern) : NetHack.Sokoban22Refined85.d7500 p = d371192 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d10 p else NetHack.Sokoban22Refined85.d8 p) = d371192 p
  rw [oldNode10, oldNode8]
  rfl
theorem oldNode7501 (p : Pattern) : NetHack.Sokoban22Refined85.d7501 p = d371193 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7500 p else NetHack.Sokoban22Refined85.d7290 p) = d371193 p
  rw [oldNode7500, oldNode7290]
  rfl
theorem oldNode7502 (p : Pattern) : NetHack.Sokoban22Refined85.d7502 p = d371194 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7501 p else NetHack.Sokoban22Refined85.d4 p) = d371194 p
  rw [oldNode7501, oldNode4]
  rfl
theorem oldNode7503 (p : Pattern) : NetHack.Sokoban22Refined85.d7503 p = d371195 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7253 p) = d371195 p
  rw [oldNode12, oldNode7253]
  rfl
theorem oldNode7504 (p : Pattern) : NetHack.Sokoban22Refined85.d7504 p = d371196 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7503 p else NetHack.Sokoban22Refined85.d7502 p) = d371196 p
  rw [oldNode7503, oldNode7502]
  rfl
theorem oldNode7505 (p : Pattern) : NetHack.Sokoban22Refined85.d7505 p = d371197 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7504 p else NetHack.Sokoban22Refined85.d7340 p) = d371197 p
  rw [oldNode7504, oldNode7340]
  rfl
theorem oldNode7506 (p : Pattern) : NetHack.Sokoban22Refined85.d7506 p = d371198 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7505 p else NetHack.Sokoban22Refined85.d7340 p) = d371198 p
  rw [oldNode7505, oldNode7340]
  rfl
theorem oldNode7507 (p : Pattern) : NetHack.Sokoban22Refined85.d7507 p = d371199 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7353 p else NetHack.Sokoban22Refined85.d7505 p) = d371199 p
  rw [oldNode7353, oldNode7505]
  rfl
theorem oldNode7508 (p : Pattern) : NetHack.Sokoban22Refined85.d7508 p = d371200 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7507 p else NetHack.Sokoban22Refined85.d7506 p) = d371200 p
  rw [oldNode7507, oldNode7506]
  rfl
theorem oldNode7509 (p : Pattern) : NetHack.Sokoban22Refined85.d7509 p = d371201 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7283 p else NetHack.Sokoban22Refined85.d7324 p) = d371201 p
  rw [oldNode7283, oldNode7324]
  rfl
theorem oldNode7510 (p : Pattern) : NetHack.Sokoban22Refined85.d7510 p = d371202 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7509 p else NetHack.Sokoban22Refined85.d7356 p) = d371202 p
  rw [oldNode7509, oldNode7356]
  rfl
theorem oldNode7511 (p : Pattern) : NetHack.Sokoban22Refined85.d7511 p = d371203 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7288 p else NetHack.Sokoban22Refined85.d7324 p) = d371203 p
  rw [oldNode7288, oldNode7324]
  rfl
theorem oldNode7512 (p : Pattern) : NetHack.Sokoban22Refined85.d7512 p = d371204 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7357 p) = d371204 p
  rw [oldNode12, oldNode7357]
  rfl
theorem oldNode7513 (p : Pattern) : NetHack.Sokoban22Refined85.d7513 p = d371205 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7512 p else NetHack.Sokoban22Refined85.d7511 p) = d371205 p
  rw [oldNode7512, oldNode7511]
  rfl
theorem oldNode7514 (p : Pattern) : NetHack.Sokoban22Refined85.d7514 p = d371206 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7513 p else NetHack.Sokoban22Refined85.d7510 p) = d371206 p
  rw [oldNode7513, oldNode7510]
  rfl
theorem oldNode7515 (p : Pattern) : NetHack.Sokoban22Refined85.d7515 p = d371207 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7512 p else NetHack.Sokoban22Refined85.d7325 p) = d371207 p
  rw [oldNode7512, oldNode7325]
  rfl
theorem oldNode7516 (p : Pattern) : NetHack.Sokoban22Refined85.d7516 p = d371208 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7332 p else NetHack.Sokoban22Refined85.d7515 p) = d371208 p
  rw [oldNode7332, oldNode7515]
  rfl
theorem oldNode7517 (p : Pattern) : NetHack.Sokoban22Refined85.d7517 p = d371209 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7516 p else NetHack.Sokoban22Refined85.d7514 p) = d371209 p
  rw [oldNode7516, oldNode7514]
  rfl
theorem oldNode7518 (p : Pattern) : NetHack.Sokoban22Refined85.d7518 p = d371210 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7517 p else NetHack.Sokoban22Refined85.d7508 p) = d371210 p
  rw [oldNode7517, oldNode7508]
  rfl
theorem oldNode7519 (p : Pattern) : NetHack.Sokoban22Refined85.d7519 p = d371211 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d8 p else NetHack.Sokoban22Refined85.d6 p) = d371211 p
  rw [oldNode8, oldNode6]
  rfl
theorem oldNode7520 (p : Pattern) : NetHack.Sokoban22Refined85.d7520 p = d371212 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7519 p else NetHack.Sokoban22Refined85.d7275 p) = d371212 p
  rw [oldNode7519, oldNode7275]
  rfl
theorem oldNode7521 (p : Pattern) : NetHack.Sokoban22Refined85.d7521 p = d371213 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7520 p else NetHack.Sokoban22Refined85.d2 p) = d371213 p
  rw [oldNode7520, oldNode2]
  rfl
theorem oldNode7522 (p : Pattern) : NetHack.Sokoban22Refined85.d7522 p = d371214 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7305 p) = d371214 p
  rw [oldNode12, oldNode7305]
  rfl
theorem oldNode7523 (p : Pattern) : NetHack.Sokoban22Refined85.d7523 p = d371215 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7522 p else NetHack.Sokoban22Refined85.d7521 p) = d371215 p
  rw [oldNode7522, oldNode7521]
  rfl
theorem oldNode7524 (p : Pattern) : NetHack.Sokoban22Refined85.d7524 p = d371216 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7523 p else NetHack.Sokoban22Refined85.d7340 p) = d371216 p
  rw [oldNode7523, oldNode7340]
  rfl
theorem oldNode7525 (p : Pattern) : NetHack.Sokoban22Refined85.d7525 p = d371217 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7352 p else NetHack.Sokoban22Refined85.d7504 p) = d371217 p
  rw [oldNode7352, oldNode7504]
  rfl
theorem oldNode7526 (p : Pattern) : NetHack.Sokoban22Refined85.d7526 p = d371218 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7525 p else NetHack.Sokoban22Refined85.d7524 p) = d371218 p
  rw [oldNode7525, oldNode7524]
  rfl
theorem oldNode7527 (p : Pattern) : NetHack.Sokoban22Refined85.d7527 p = d371219 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7317 p else NetHack.Sokoban22Refined85.d7504 p) = d371219 p
  rw [oldNode7317, oldNode7504]
  rfl
theorem oldNode7528 (p : Pattern) : NetHack.Sokoban22Refined85.d7528 p = d371220 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7321 p else NetHack.Sokoban22Refined85.d7527 p) = d371220 p
  rw [oldNode7321, oldNode7527]
  rfl
theorem oldNode7529 (p : Pattern) : NetHack.Sokoban22Refined85.d7529 p = d371221 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7528 p else NetHack.Sokoban22Refined85.d7526 p) = d371221 p
  rw [oldNode7528, oldNode7526]
  rfl
theorem oldNode7530 (p : Pattern) : NetHack.Sokoban22Refined85.d7530 p = d371222 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7294 p else NetHack.Sokoban22Refined85.d7509 p) = d371222 p
  rw [oldNode7294, oldNode7509]
  rfl
theorem oldNode7531 (p : Pattern) : NetHack.Sokoban22Refined85.d7531 p = d371223 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7331 p else NetHack.Sokoban22Refined85.d7512 p) = d371223 p
  rw [oldNode7331, oldNode7512]
  rfl
theorem oldNode7532 (p : Pattern) : NetHack.Sokoban22Refined85.d7532 p = d371224 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7531 p else NetHack.Sokoban22Refined85.d7530 p) = d371224 p
  rw [oldNode7531, oldNode7530]
  rfl
theorem oldNode7533 (p : Pattern) : NetHack.Sokoban22Refined85.d7533 p = d371225 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7512 p) = d371225 p
  rw [oldNode12, oldNode7512]
  rfl
theorem oldNode7534 (p : Pattern) : NetHack.Sokoban22Refined85.d7534 p = d371226 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7533 p) = d371226 p
  rw [oldNode12, oldNode7533]
  rfl
theorem oldNode7535 (p : Pattern) : NetHack.Sokoban22Refined85.d7535 p = d371227 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7534 p else NetHack.Sokoban22Refined85.d7532 p) = d371227 p
  rw [oldNode7534, oldNode7532]
  rfl
theorem oldNode7536 (p : Pattern) : NetHack.Sokoban22Refined85.d7536 p = d371228 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7535 p else NetHack.Sokoban22Refined85.d7529 p) = d371228 p
  rw [oldNode7535, oldNode7529]
  rfl
theorem oldNode7537 (p : Pattern) : NetHack.Sokoban22Refined85.d7537 p = d371229 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7536 p else NetHack.Sokoban22Refined85.d7518 p) = d371229 p
  rw [oldNode7536, oldNode7518]
  rfl
theorem oldNode7538 (p : Pattern) : NetHack.Sokoban22Refined85.d7538 p = d371230 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7341 p else NetHack.Sokoban22Refined85.d0 p) = d371230 p
  rw [oldNode7341, oldNode0]
  rfl
theorem oldNode7539 (p : Pattern) : NetHack.Sokoban22Refined85.d7539 p = d371231 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7337 p) = d371231 p
  rw [oldNode12, oldNode7337]
  rfl
theorem oldNode7540 (p : Pattern) : NetHack.Sokoban22Refined85.d7540 p = d371232 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7539 p else NetHack.Sokoban22Refined85.d7538 p) = d371232 p
  rw [oldNode7539, oldNode7538]
  rfl
theorem oldNode7541 (p : Pattern) : NetHack.Sokoban22Refined85.d7541 p = d371233 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7346 p else NetHack.Sokoban22Refined85.d7540 p) = d371233 p
  rw [oldNode7346, oldNode7540]
  rfl
theorem oldNode7542 (p : Pattern) : NetHack.Sokoban22Refined85.d7542 p = d371234 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7359 p else NetHack.Sokoban22Refined85.d7541 p) = d371234 p
  rw [oldNode7359, oldNode7541]
  rfl
theorem oldNode7543 (p : Pattern) : NetHack.Sokoban22Refined85.d7543 p = d371235 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7360 p else NetHack.Sokoban22Refined85.d7542 p) = d371235 p
  rw [oldNode7360, oldNode7542]
  rfl
theorem oldNode7544 (p : Pattern) : NetHack.Sokoban22Refined85.d7544 p = d371236 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7291 p) = d371236 p
  rw [oldNode12, oldNode7291]
  rfl
theorem oldNode7545 (p : Pattern) : NetHack.Sokoban22Refined85.d7545 p = d371237 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7544 p else NetHack.Sokoban22Refined85.d8 p) = d371237 p
  rw [oldNode7544, oldNode8]
  rfl
theorem oldNode7546 (p : Pattern) : NetHack.Sokoban22Refined85.d7546 p = d371238 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7544 p) = d371238 p
  rw [oldNode12, oldNode7544]
  rfl
theorem oldNode7547 (p : Pattern) : NetHack.Sokoban22Refined85.d7547 p = d371239 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7546 p else NetHack.Sokoban22Refined85.d7545 p) = d371239 p
  rw [oldNode7546, oldNode7545]
  rfl
theorem oldNode7548 (p : Pattern) : NetHack.Sokoban22Refined85.d7548 p = d371240 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7547 p else NetHack.Sokoban22Refined85.d7348 p) = d371240 p
  rw [oldNode7547, oldNode7348]
  rfl
theorem oldNode7549 (p : Pattern) : NetHack.Sokoban22Refined85.d7549 p = d371241 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7548 p) = d371241 p
  rw [oldNode12, oldNode7548]
  rfl
theorem oldNode7550 (p : Pattern) : NetHack.Sokoban22Refined85.d7550 p = d371242 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7549 p) = d371242 p
  rw [oldNode12, oldNode7549]
  rfl
theorem oldNode7551 (p : Pattern) : NetHack.Sokoban22Refined85.d7551 p = d371243 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7550 p else NetHack.Sokoban22Refined85.d7543 p) = d371243 p
  rw [oldNode7550, oldNode7543]
  rfl
theorem oldNode7552 (p : Pattern) : NetHack.Sokoban22Refined85.d7552 p = d371244 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d10 p else NetHack.Sokoban22Refined85.d6 p) = d371244 p
  rw [oldNode10, oldNode6]
  rfl
theorem oldNode7553 (p : Pattern) : NetHack.Sokoban22Refined85.d7553 p = d371245 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7552 p else NetHack.Sokoban22Refined85.d7275 p) = d371245 p
  rw [oldNode7552, oldNode7275]
  rfl
theorem oldNode7554 (p : Pattern) : NetHack.Sokoban22Refined85.d7554 p = d371246 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7553 p) = d371246 p
  rw [oldNode12, oldNode7553]
  rfl
theorem oldNode7555 (p : Pattern) : NetHack.Sokoban22Refined85.d7555 p = d371247 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7554 p else NetHack.Sokoban22Refined85.d7324 p) = d371247 p
  rw [oldNode7554, oldNode7324]
  rfl
theorem oldNode7556 (p : Pattern) : NetHack.Sokoban22Refined85.d7556 p = d371248 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7356 p else NetHack.Sokoban22Refined85.d7555 p) = d371248 p
  rw [oldNode7356, oldNode7555]
  rfl
theorem oldNode7557 (p : Pattern) : NetHack.Sokoban22Refined85.d7557 p = d371249 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7320 p else NetHack.Sokoban22Refined85.d7348 p) = d371249 p
  rw [oldNode7320, oldNode7348]
  rfl
theorem oldNode7558 (p : Pattern) : NetHack.Sokoban22Refined85.d7558 p = d371250 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7557 p else NetHack.Sokoban22Refined85.d7556 p) = d371250 p
  rw [oldNode7557, oldNode7556]
  rfl
theorem oldNode7559 (p : Pattern) : NetHack.Sokoban22Refined85.d7559 p = d371251 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7370 p else NetHack.Sokoban22Refined85.d7558 p) = d371251 p
  rw [oldNode7370, oldNode7558]
  rfl
theorem oldNode7560 (p : Pattern) : NetHack.Sokoban22Refined85.d7560 p = d371252 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7547 p) = d371252 p
  rw [oldNode12, oldNode7547]
  rfl
theorem oldNode7561 (p : Pattern) : NetHack.Sokoban22Refined85.d7561 p = d371253 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7560 p) = d371253 p
  rw [oldNode12, oldNode7560]
  rfl
theorem oldNode7562 (p : Pattern) : NetHack.Sokoban22Refined85.d7562 p = d371254 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7561 p) = d371254 p
  rw [oldNode12, oldNode7561]
  rfl
theorem oldNode7563 (p : Pattern) : NetHack.Sokoban22Refined85.d7563 p = d371255 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7562 p else NetHack.Sokoban22Refined85.d7559 p) = d371255 p
  rw [oldNode7562, oldNode7559]
  rfl
theorem oldNode7564 (p : Pattern) : NetHack.Sokoban22Refined85.d7564 p = d371256 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7563 p else NetHack.Sokoban22Refined85.d7551 p) = d371256 p
  rw [oldNode7563, oldNode7551]
  rfl
theorem oldNode7565 (p : Pattern) : NetHack.Sokoban22Refined85.d7565 p = d371257 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d7564 p else NetHack.Sokoban22Refined85.d7537 p) = d371257 p
  rw [oldNode7564, oldNode7537]
  rfl
theorem oldNode7566 (p : Pattern) : NetHack.Sokoban22Refined85.d7566 p = d371258 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7564 p) = d371258 p
  rw [oldNode12, oldNode7564]
  rfl
theorem oldNode7567 (p : Pattern) : NetHack.Sokoban22Refined85.d7567 p = d371259 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d7566 p else NetHack.Sokoban22Refined85.d7565 p) = d371259 p
  rw [oldNode7566, oldNode7565]
  rfl
theorem oldNode7568 (p : Pattern) : NetHack.Sokoban22Refined85.d7568 p = d371260 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d7567 p else NetHack.Sokoban22Refined85.d7384 p) = d371260 p
  rw [oldNode7567, oldNode7384]
  rfl
theorem oldNode7569 (p : Pattern) : NetHack.Sokoban22Refined85.d7569 p = d371261 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d7568 p else NetHack.Sokoban22Refined85.d7387 p) = d371261 p
  rw [oldNode7568, oldNode7387]
  rfl
theorem oldNode7570 (p : Pattern) : NetHack.Sokoban22Refined85.d7570 p = d371262 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7401 p) = d371262 p
  rw [oldNode12, oldNode7401]
  rfl
theorem oldNode7571 (p : Pattern) : NetHack.Sokoban22Refined85.d7571 p = d371263 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7570 p else NetHack.Sokoban22Refined85.d7438 p) = d371263 p
  rw [oldNode7570, oldNode7438]
  rfl
theorem oldNode7572 (p : Pattern) : NetHack.Sokoban22Refined85.d7572 p = d371264 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7570 p) = d371264 p
  rw [oldNode12, oldNode7570]
  rfl
theorem oldNode7573 (p : Pattern) : NetHack.Sokoban22Refined85.d7573 p = d371265 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7572 p else NetHack.Sokoban22Refined85.d7571 p) = d371265 p
  rw [oldNode7572, oldNode7571]
  rfl
theorem oldNode7574 (p : Pattern) : NetHack.Sokoban22Refined85.d7574 p = d371266 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7424 p) = d371266 p
  rw [oldNode12, oldNode7424]
  rfl
theorem oldNode7575 (p : Pattern) : NetHack.Sokoban22Refined85.d7575 p = d371267 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7574 p else NetHack.Sokoban22Refined85.d7446 p) = d371267 p
  rw [oldNode7574, oldNode7446]
  rfl
theorem oldNode7576 (p : Pattern) : NetHack.Sokoban22Refined85.d7576 p = d371268 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7574 p) = d371268 p
  rw [oldNode12, oldNode7574]
  rfl
theorem oldNode7577 (p : Pattern) : NetHack.Sokoban22Refined85.d7577 p = d371269 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7576 p else NetHack.Sokoban22Refined85.d7575 p) = d371269 p
  rw [oldNode7576, oldNode7575]
  rfl
theorem oldNode7578 (p : Pattern) : NetHack.Sokoban22Refined85.d7578 p = d371270 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7577 p else NetHack.Sokoban22Refined85.d7573 p) = d371270 p
  rw [oldNode7577, oldNode7573]
  rfl
theorem oldNode7579 (p : Pattern) : NetHack.Sokoban22Refined85.d7579 p = d371271 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7578 p else NetHack.Sokoban22Refined85.d7430 p) = d371271 p
  rw [oldNode7578, oldNode7430]
  rfl
theorem oldNode7580 (p : Pattern) : NetHack.Sokoban22Refined85.d7580 p = d371272 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7465 p) = d371272 p
  rw [oldNode12, oldNode7465]
  rfl
theorem oldNode7581 (p : Pattern) : NetHack.Sokoban22Refined85.d7581 p = d371273 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7580 p else NetHack.Sokoban22Refined85.d7477 p) = d371273 p
  rw [oldNode7580, oldNode7477]
  rfl
theorem oldNode7582 (p : Pattern) : NetHack.Sokoban22Refined85.d7582 p = d371274 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7580 p) = d371274 p
  rw [oldNode12, oldNode7580]
  rfl
theorem oldNode7583 (p : Pattern) : NetHack.Sokoban22Refined85.d7583 p = d371275 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7582 p else NetHack.Sokoban22Refined85.d7581 p) = d371275 p
  rw [oldNode7582, oldNode7581]
  rfl
theorem oldNode7584 (p : Pattern) : NetHack.Sokoban22Refined85.d7584 p = d371276 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7485 p else NetHack.Sokoban22Refined85.d7583 p) = d371276 p
  rw [oldNode7485, oldNode7583]
  rfl
theorem oldNode7585 (p : Pattern) : NetHack.Sokoban22Refined85.d7585 p = d371277 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7584 p else NetHack.Sokoban22Refined85.d7476 p) = d371277 p
  rw [oldNode7584, oldNode7476]
  rfl
theorem oldNode7586 (p : Pattern) : NetHack.Sokoban22Refined85.d7586 p = d371278 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d7585 p else NetHack.Sokoban22Refined85.d7579 p) = d371278 p
  rw [oldNode7585, oldNode7579]
  rfl
theorem oldNode7587 (p : Pattern) : NetHack.Sokoban22Refined85.d7587 p = d371279 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d7492 p else NetHack.Sokoban22Refined85.d7585 p) = d371279 p
  rw [oldNode7492, oldNode7585]
  rfl
theorem oldNode7588 (p : Pattern) : NetHack.Sokoban22Refined85.d7588 p = d371280 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d7587 p else NetHack.Sokoban22Refined85.d7586 p) = d371280 p
  rw [oldNode7587, oldNode7586]
  rfl
theorem oldNode7589 (p : Pattern) : NetHack.Sokoban22Refined85.d7589 p = d371281 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7458 p else NetHack.Sokoban22Refined85.d1 p) = d371281 p
  rw [oldNode7458, oldNode1]
  rfl
theorem oldNode7590 (p : Pattern) : NetHack.Sokoban22Refined85.d7590 p = d371282 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7454 p) = d371282 p
  rw [oldNode12, oldNode7454]
  rfl
theorem oldNode7591 (p : Pattern) : NetHack.Sokoban22Refined85.d7591 p = d371283 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7590 p else NetHack.Sokoban22Refined85.d7589 p) = d371283 p
  rw [oldNode7590, oldNode7589]
  rfl
theorem oldNode7592 (p : Pattern) : NetHack.Sokoban22Refined85.d7592 p = d371284 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7465 p else NetHack.Sokoban22Refined85.d7591 p) = d371284 p
  rw [oldNode7465, oldNode7591]
  rfl
theorem oldNode7593 (p : Pattern) : NetHack.Sokoban22Refined85.d7593 p = d371285 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7592 p else NetHack.Sokoban22Refined85.d7457 p) = d371285 p
  rw [oldNode7592, oldNode7457]
  rfl
theorem oldNode7594 (p : Pattern) : NetHack.Sokoban22Refined85.d7594 p = d371286 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7465 p else NetHack.Sokoban22Refined85.d7460 p) = d371286 p
  rw [oldNode7465, oldNode7460]
  rfl
theorem oldNode7595 (p : Pattern) : NetHack.Sokoban22Refined85.d7595 p = d371287 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7404 p else NetHack.Sokoban22Refined85.d7594 p) = d371287 p
  rw [oldNode7404, oldNode7594]
  rfl
theorem oldNode7596 (p : Pattern) : NetHack.Sokoban22Refined85.d7596 p = d371288 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7595 p else NetHack.Sokoban22Refined85.d7593 p) = d371288 p
  rw [oldNode7595, oldNode7593]
  rfl
theorem oldNode7597 (p : Pattern) : NetHack.Sokoban22Refined85.d7597 p = d371289 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7417 p else NetHack.Sokoban22Refined85.d7444 p) = d371289 p
  rw [oldNode7417, oldNode7444]
  rfl
theorem oldNode7598 (p : Pattern) : NetHack.Sokoban22Refined85.d7598 p = d371290 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7597 p else NetHack.Sokoban22Refined85.d7470 p) = d371290 p
  rw [oldNode7597, oldNode7470]
  rfl
theorem oldNode7599 (p : Pattern) : NetHack.Sokoban22Refined85.d7599 p = d371291 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7574 p else NetHack.Sokoban22Refined85.d7598 p) = d371291 p
  rw [oldNode7574, oldNode7598]
  rfl
theorem oldNode7600 (p : Pattern) : NetHack.Sokoban22Refined85.d7600 p = d371292 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7471 p) = d371292 p
  rw [oldNode12, oldNode7471]
  rfl
theorem oldNode7601 (p : Pattern) : NetHack.Sokoban22Refined85.d7601 p = d371293 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7600 p) = d371293 p
  rw [oldNode12, oldNode7600]
  rfl
theorem oldNode7602 (p : Pattern) : NetHack.Sokoban22Refined85.d7602 p = d371294 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7601 p) = d371294 p
  rw [oldNode12, oldNode7601]
  rfl
theorem oldNode7603 (p : Pattern) : NetHack.Sokoban22Refined85.d7603 p = d371295 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7602 p else NetHack.Sokoban22Refined85.d7599 p) = d371295 p
  rw [oldNode7602, oldNode7599]
  rfl
theorem oldNode7604 (p : Pattern) : NetHack.Sokoban22Refined85.d7604 p = d371296 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7603 p else NetHack.Sokoban22Refined85.d7596 p) = d371296 p
  rw [oldNode7603, oldNode7596]
  rfl
theorem oldNode7605 (p : Pattern) : NetHack.Sokoban22Refined85.d7605 p = d371297 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d9 p else NetHack.Sokoban22Refined85.d7 p) = d371297 p
  rw [oldNode9, oldNode7]
  rfl
theorem oldNode7606 (p : Pattern) : NetHack.Sokoban22Refined85.d7606 p = d371298 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7605 p else NetHack.Sokoban22Refined85.d7411 p) = d371298 p
  rw [oldNode7605, oldNode7411]
  rfl
theorem oldNode7607 (p : Pattern) : NetHack.Sokoban22Refined85.d7607 p = d371299 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7606 p else NetHack.Sokoban22Refined85.d3 p) = d371299 p
  rw [oldNode7606, oldNode3]
  rfl
theorem oldNode7608 (p : Pattern) : NetHack.Sokoban22Refined85.d7608 p = d371300 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7432 p) = d371300 p
  rw [oldNode12, oldNode7432]
  rfl
theorem oldNode7609 (p : Pattern) : NetHack.Sokoban22Refined85.d7609 p = d371301 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7608 p else NetHack.Sokoban22Refined85.d7607 p) = d371301 p
  rw [oldNode7608, oldNode7607]
  rfl
theorem oldNode7610 (p : Pattern) : NetHack.Sokoban22Refined85.d7610 p = d371302 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7609 p else NetHack.Sokoban22Refined85.d7591 p) = d371302 p
  rw [oldNode7609, oldNode7591]
  rfl
theorem oldNode7611 (p : Pattern) : NetHack.Sokoban22Refined85.d7611 p = d371303 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7264 p else NetHack.Sokoban22Refined85.d7421 p) = d371303 p
  rw [oldNode7264, oldNode7421]
  rfl
theorem oldNode7612 (p : Pattern) : NetHack.Sokoban22Refined85.d7612 p = d371304 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7611 p else NetHack.Sokoban22Refined85.d5 p) = d371304 p
  rw [oldNode7611, oldNode5]
  rfl
theorem oldNode7613 (p : Pattern) : NetHack.Sokoban22Refined85.d7613 p = d371305 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7396 p) = d371305 p
  rw [oldNode12, oldNode7396]
  rfl
theorem oldNode7614 (p : Pattern) : NetHack.Sokoban22Refined85.d7614 p = d371306 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7613 p else NetHack.Sokoban22Refined85.d7612 p) = d371306 p
  rw [oldNode7613, oldNode7612]
  rfl
theorem oldNode7615 (p : Pattern) : NetHack.Sokoban22Refined85.d7615 p = d371307 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7614 p) = d371307 p
  rw [oldNode12, oldNode7614]
  rfl
theorem oldNode7616 (p : Pattern) : NetHack.Sokoban22Refined85.d7616 p = d371308 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7615 p else NetHack.Sokoban22Refined85.d7610 p) = d371308 p
  rw [oldNode7615, oldNode7610]
  rfl
theorem oldNode7617 (p : Pattern) : NetHack.Sokoban22Refined85.d7617 p = d371309 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7611 p) = d371309 p
  rw [oldNode12, oldNode7611]
  rfl
theorem oldNode7618 (p : Pattern) : NetHack.Sokoban22Refined85.d7618 p = d371310 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7617 p else NetHack.Sokoban22Refined85.d7423 p) = d371310 p
  rw [oldNode7617, oldNode7423]
  rfl
theorem oldNode7619 (p : Pattern) : NetHack.Sokoban22Refined85.d7619 p = d371311 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7618 p) = d371311 p
  rw [oldNode12, oldNode7618]
  rfl
theorem oldNode7620 (p : Pattern) : NetHack.Sokoban22Refined85.d7620 p = d371312 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7619 p) = d371312 p
  rw [oldNode12, oldNode7619]
  rfl
theorem oldNode7621 (p : Pattern) : NetHack.Sokoban22Refined85.d7621 p = d371313 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7620 p else NetHack.Sokoban22Refined85.d7616 p) = d371313 p
  rw [oldNode7620, oldNode7616]
  rfl
theorem oldNode7622 (p : Pattern) : NetHack.Sokoban22Refined85.d7622 p = d371314 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7417 p else NetHack.Sokoban22Refined85.d7423 p) = d371314 p
  rw [oldNode7417, oldNode7423]
  rfl
theorem oldNode7623 (p : Pattern) : NetHack.Sokoban22Refined85.d7623 p = d371315 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7424 p else NetHack.Sokoban22Refined85.d7622 p) = d371315 p
  rw [oldNode7424, oldNode7622]
  rfl
theorem oldNode7624 (p : Pattern) : NetHack.Sokoban22Refined85.d7624 p = d371316 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7601 p else NetHack.Sokoban22Refined85.d7623 p) = d371316 p
  rw [oldNode7601, oldNode7623]
  rfl
theorem oldNode7625 (p : Pattern) : NetHack.Sokoban22Refined85.d7625 p = d371317 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7300 p) = d371317 p
  rw [oldNode12, oldNode7300]
  rfl
theorem oldNode7626 (p : Pattern) : NetHack.Sokoban22Refined85.d7626 p = d371318 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7625 p else NetHack.Sokoban22Refined85.d7624 p) = d371318 p
  rw [oldNode7625, oldNode7624]
  rfl
theorem oldNode7627 (p : Pattern) : NetHack.Sokoban22Refined85.d7627 p = d371319 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7626 p else NetHack.Sokoban22Refined85.d7621 p) = d371319 p
  rw [oldNode7626, oldNode7621]
  rfl
theorem oldNode7628 (p : Pattern) : NetHack.Sokoban22Refined85.d7628 p = d371320 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7627 p else NetHack.Sokoban22Refined85.d7604 p) = d371320 p
  rw [oldNode7627, oldNode7604]
  rfl
theorem oldNode7629 (p : Pattern) : NetHack.Sokoban22Refined85.d7629 p = d371321 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7463 p else NetHack.Sokoban22Refined85.d7460 p) = d371321 p
  rw [oldNode7463, oldNode7460]
  rfl
theorem oldNode7630 (p : Pattern) : NetHack.Sokoban22Refined85.d7630 p = d371322 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7320 p else NetHack.Sokoban22Refined85.d7470 p) = d371322 p
  rw [oldNode7320, oldNode7470]
  rfl
theorem oldNode7631 (p : Pattern) : NetHack.Sokoban22Refined85.d7631 p = d371323 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7630 p else NetHack.Sokoban22Refined85.d7629 p) = d371323 p
  rw [oldNode7630, oldNode7629]
  rfl
theorem oldNode7632 (p : Pattern) : NetHack.Sokoban22Refined85.d7632 p = d371324 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7481 p else NetHack.Sokoban22Refined85.d7631 p) = d371324 p
  rw [oldNode7481, oldNode7631]
  rfl
theorem oldNode7633 (p : Pattern) : NetHack.Sokoban22Refined85.d7633 p = d371325 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7485 p else NetHack.Sokoban22Refined85.d7632 p) = d371325 p
  rw [oldNode7485, oldNode7632]
  rfl
theorem oldNode7634 (p : Pattern) : NetHack.Sokoban22Refined85.d7634 p = d371326 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d11 p else NetHack.Sokoban22Refined85.d7 p) = d371326 p
  rw [oldNode11, oldNode7]
  rfl
theorem oldNode7635 (p : Pattern) : NetHack.Sokoban22Refined85.d7635 p = d371327 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7634 p else NetHack.Sokoban22Refined85.d7411 p) = d371327 p
  rw [oldNode7634, oldNode7411]
  rfl
theorem oldNode7636 (p : Pattern) : NetHack.Sokoban22Refined85.d7636 p = d371328 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7635 p) = d371328 p
  rw [oldNode12, oldNode7635]
  rfl
theorem oldNode7637 (p : Pattern) : NetHack.Sokoban22Refined85.d7637 p = d371329 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7636 p else NetHack.Sokoban22Refined85.d7444 p) = d371329 p
  rw [oldNode7636, oldNode7444]
  rfl
theorem oldNode7638 (p : Pattern) : NetHack.Sokoban22Refined85.d7638 p = d371330 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7470 p else NetHack.Sokoban22Refined85.d7637 p) = d371330 p
  rw [oldNode7470, oldNode7637]
  rfl
theorem oldNode7639 (p : Pattern) : NetHack.Sokoban22Refined85.d7639 p = d371331 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7580 p else NetHack.Sokoban22Refined85.d7638 p) = d371331 p
  rw [oldNode7580, oldNode7638]
  rfl
theorem oldNode7640 (p : Pattern) : NetHack.Sokoban22Refined85.d7640 p = d371332 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7484 p else NetHack.Sokoban22Refined85.d7639 p) = d371332 p
  rw [oldNode7484, oldNode7639]
  rfl
theorem oldNode7641 (p : Pattern) : NetHack.Sokoban22Refined85.d7641 p = d371333 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7353 p) = d371333 p
  rw [oldNode12, oldNode7353]
  rfl
theorem oldNode7642 (p : Pattern) : NetHack.Sokoban22Refined85.d7642 p = d371334 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7641 p) = d371334 p
  rw [oldNode12, oldNode7641]
  rfl
theorem oldNode7643 (p : Pattern) : NetHack.Sokoban22Refined85.d7643 p = d371335 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7642 p else NetHack.Sokoban22Refined85.d7640 p) = d371335 p
  rw [oldNode7642, oldNode7640]
  rfl
theorem oldNode7644 (p : Pattern) : NetHack.Sokoban22Refined85.d7644 p = d371336 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7643 p else NetHack.Sokoban22Refined85.d7633 p) = d371336 p
  rw [oldNode7643, oldNode7633]
  rfl
theorem oldNode7645 (p : Pattern) : NetHack.Sokoban22Refined85.d7645 p = d371337 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d7644 p else NetHack.Sokoban22Refined85.d7628 p) = d371337 p
  rw [oldNode7644, oldNode7628]
  rfl
theorem oldNode7646 (p : Pattern) : NetHack.Sokoban22Refined85.d7646 p = d371338 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7352 p else NetHack.Sokoban22Refined85.d7470 p) = d371338 p
  rw [oldNode7352, oldNode7470]
  rfl
theorem oldNode7647 (p : Pattern) : NetHack.Sokoban22Refined85.d7647 p = d371339 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7646 p else NetHack.Sokoban22Refined85.d7629 p) = d371339 p
  rw [oldNode7646, oldNode7629]
  rfl
theorem oldNode7648 (p : Pattern) : NetHack.Sokoban22Refined85.d7648 p = d371340 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7352 p else NetHack.Sokoban22Refined85.d7465 p) = d371340 p
  rw [oldNode7352, oldNode7465]
  rfl
theorem oldNode7649 (p : Pattern) : NetHack.Sokoban22Refined85.d7649 p = d371341 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7648 p) = d371341 p
  rw [oldNode12, oldNode7648]
  rfl
theorem oldNode7650 (p : Pattern) : NetHack.Sokoban22Refined85.d7650 p = d371342 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7649 p else NetHack.Sokoban22Refined85.d7647 p) = d371342 p
  rw [oldNode7649, oldNode7647]
  rfl
theorem oldNode7651 (p : Pattern) : NetHack.Sokoban22Refined85.d7651 p = d371343 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7320 p else NetHack.Sokoban22Refined85.d7472 p) = d371343 p
  rw [oldNode7320, oldNode7472]
  rfl
theorem oldNode7652 (p : Pattern) : NetHack.Sokoban22Refined85.d7652 p = d371344 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7651 p) = d371344 p
  rw [oldNode12, oldNode7651]
  rfl
theorem oldNode7653 (p : Pattern) : NetHack.Sokoban22Refined85.d7653 p = d371345 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7652 p) = d371345 p
  rw [oldNode12, oldNode7652]
  rfl
theorem oldNode7654 (p : Pattern) : NetHack.Sokoban22Refined85.d7654 p = d371346 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d7653 p else NetHack.Sokoban22Refined85.d7650 p) = d371346 p
  rw [oldNode7653, oldNode7650]
  rfl
theorem oldNode7655 (p : Pattern) : NetHack.Sokoban22Refined85.d7655 p = d371347 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d7643 p else NetHack.Sokoban22Refined85.d7654 p) = d371347 p
  rw [oldNode7643, oldNode7654]
  rfl
theorem oldNode7656 (p : Pattern) : NetHack.Sokoban22Refined85.d7656 p = d371348 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7655 p) = d371348 p
  rw [oldNode12, oldNode7655]
  rfl
theorem oldNode7657 (p : Pattern) : NetHack.Sokoban22Refined85.d7657 p = d371349 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d7656 p else NetHack.Sokoban22Refined85.d7645 p) = d371349 p
  rw [oldNode7656, oldNode7645]
  rfl
theorem oldNode7658 (p : Pattern) : NetHack.Sokoban22Refined85.d7658 p = d371350 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d7657 p else NetHack.Sokoban22Refined85.d7588 p) = d371350 p
  rw [oldNode7657, oldNode7588]
  rfl
theorem oldNode7659 (p : Pattern) : NetHack.Sokoban22Refined85.d7659 p = d371351 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d7658 p else NetHack.Sokoban22Refined85.d7387 p) = d371351 p
  rw [oldNode7658, oldNode7387]
  rfl
theorem oldNode7660 (p : Pattern) : NetHack.Sokoban22Refined85.d7660 p = d371352 p := by
  change (if p 49 then NetHack.Sokoban22Refined85.d7659 p else NetHack.Sokoban22Refined85.d7569 p) = d371352 p
  rw [oldNode7659, oldNode7569]
  rfl
theorem oldNode7661 (p : Pattern) : NetHack.Sokoban22Refined85.d7661 p = d371353 p := by
  change (if p 48 then NetHack.Sokoban22Refined85.d7660 p else NetHack.Sokoban22Refined85.d7499 p) = d371353 p
  rw [oldNode7660, oldNode7499]
  rfl
theorem oldNode7662 (p : Pattern) : NetHack.Sokoban22Refined85.d7662 p = d375868 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3239 p else NetHack.Sokoban22Refined85.d3226 p) = d375868 p
  rw [oldNode3239, oldNode3226]
  rfl
theorem oldNode7663 (p : Pattern) : NetHack.Sokoban22Refined85.d7663 p = d375869 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d3239 p else NetHack.Sokoban22Refined85.d7662 p) = d375869 p
  rw [oldNode3239, oldNode7662]
  rfl
theorem oldNode7664 (p : Pattern) : NetHack.Sokoban22Refined85.d7664 p = d375870 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7663 p else NetHack.Sokoban22Refined85.d3226 p) = d375870 p
  rw [oldNode7663, oldNode3226]
  rfl
theorem oldNode7665 (p : Pattern) : NetHack.Sokoban22Refined85.d7665 p = d375871 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3250 p else NetHack.Sokoban22Refined85.d3226 p) = d375871 p
  rw [oldNode3250, oldNode3226]
  rfl
theorem oldNode7666 (p : Pattern) : NetHack.Sokoban22Refined85.d7666 p = d375872 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d3250 p else NetHack.Sokoban22Refined85.d7665 p) = d375872 p
  rw [oldNode3250, oldNode7665]
  rfl
theorem oldNode7667 (p : Pattern) : NetHack.Sokoban22Refined85.d7667 p = d375873 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7666 p) = d375873 p
  rw [oldNode12, oldNode7666]
  rfl
theorem oldNode7668 (p : Pattern) : NetHack.Sokoban22Refined85.d7668 p = d375874 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7667 p else NetHack.Sokoban22Refined85.d7664 p) = d375874 p
  rw [oldNode7667, oldNode7664]
  rfl
theorem oldNode7669 (p : Pattern) : NetHack.Sokoban22Refined85.d7669 p = d375875 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3461 p else NetHack.Sokoban22Refined85.d3239 p) = d375875 p
  rw [oldNode3461, oldNode3239]
  rfl
theorem oldNode7670 (p : Pattern) : NetHack.Sokoban22Refined85.d7670 p = d375876 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d3461 p else NetHack.Sokoban22Refined85.d7669 p) = d375876 p
  rw [oldNode3461, oldNode7669]
  rfl
theorem oldNode7671 (p : Pattern) : NetHack.Sokoban22Refined85.d7671 p = d375877 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7670 p else NetHack.Sokoban22Refined85.d3239 p) = d375877 p
  rw [oldNode7670, oldNode3239]
  rfl
theorem oldNode7672 (p : Pattern) : NetHack.Sokoban22Refined85.d7672 p = d375878 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3253 p else NetHack.Sokoban22Refined85.d3239 p) = d375878 p
  rw [oldNode3253, oldNode3239]
  rfl
theorem oldNode7673 (p : Pattern) : NetHack.Sokoban22Refined85.d7673 p = d375879 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d3253 p else NetHack.Sokoban22Refined85.d7672 p) = d375879 p
  rw [oldNode3253, oldNode7672]
  rfl
theorem oldNode7674 (p : Pattern) : NetHack.Sokoban22Refined85.d7674 p = d375880 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7673 p) = d375880 p
  rw [oldNode12, oldNode7673]
  rfl
theorem oldNode7675 (p : Pattern) : NetHack.Sokoban22Refined85.d7675 p = d375881 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7674 p else NetHack.Sokoban22Refined85.d7671 p) = d375881 p
  rw [oldNode7674, oldNode7671]
  rfl
theorem oldNode7676 (p : Pattern) : NetHack.Sokoban22Refined85.d7676 p = d375882 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7675 p else NetHack.Sokoban22Refined85.d7668 p) = d375882 p
  rw [oldNode7675, oldNode7668]
  rfl
theorem oldNode7677 (p : Pattern) : NetHack.Sokoban22Refined85.d7677 p = d375883 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7676 p else NetHack.Sokoban22Refined85.d7668 p) = d375883 p
  rw [oldNode7676, oldNode7668]
  rfl
theorem oldNode7678 (p : Pattern) : NetHack.Sokoban22Refined85.d7678 p = d375884 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d3244 p) = d375884 p
  rw [oldNode12, oldNode3244]
  rfl
theorem oldNode7679 (p : Pattern) : NetHack.Sokoban22Refined85.d7679 p = d375885 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7678 p) = d375885 p
  rw [oldNode12, oldNode7678]
  rfl
theorem oldNode7680 (p : Pattern) : NetHack.Sokoban22Refined85.d7680 p = d375886 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7679 p else NetHack.Sokoban22Refined85.d3244 p) = d375886 p
  rw [oldNode7679, oldNode3244]
  rfl
theorem oldNode7681 (p : Pattern) : NetHack.Sokoban22Refined85.d7681 p = d375887 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3257 p else NetHack.Sokoban22Refined85.d3244 p) = d375887 p
  rw [oldNode3257, oldNode3244]
  rfl
theorem oldNode7682 (p : Pattern) : NetHack.Sokoban22Refined85.d7682 p = d375888 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d3257 p else NetHack.Sokoban22Refined85.d7681 p) = d375888 p
  rw [oldNode3257, oldNode7681]
  rfl
theorem oldNode7683 (p : Pattern) : NetHack.Sokoban22Refined85.d7683 p = d375889 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7682 p) = d375889 p
  rw [oldNode12, oldNode7682]
  rfl
theorem oldNode7684 (p : Pattern) : NetHack.Sokoban22Refined85.d7684 p = d375890 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7683 p else NetHack.Sokoban22Refined85.d7680 p) = d375890 p
  rw [oldNode7683, oldNode7680]
  rfl
theorem oldNode7685 (p : Pattern) : NetHack.Sokoban22Refined85.d7685 p = d375891 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7684 p) = d375891 p
  rw [oldNode12, oldNode7684]
  rfl
theorem oldNode7686 (p : Pattern) : NetHack.Sokoban22Refined85.d7686 p = d375892 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d7685 p else NetHack.Sokoban22Refined85.d7676 p) = d375892 p
  rw [oldNode7685, oldNode7676]
  rfl
theorem oldNode7687 (p : Pattern) : NetHack.Sokoban22Refined85.d7687 p = d375893 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d7686 p else NetHack.Sokoban22Refined85.d7677 p) = d375893 p
  rw [oldNode7686, oldNode7677]
  rfl
theorem oldNode7688 (p : Pattern) : NetHack.Sokoban22Refined85.d7688 p = d375894 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3253 p else NetHack.Sokoban22Refined85.d3226 p) = d375894 p
  rw [oldNode3253, oldNode3226]
  rfl
theorem oldNode7689 (p : Pattern) : NetHack.Sokoban22Refined85.d7689 p = d375895 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3257 p else NetHack.Sokoban22Refined85.d3239 p) = d375895 p
  rw [oldNode3257, oldNode3239]
  rfl
theorem oldNode7690 (p : Pattern) : NetHack.Sokoban22Refined85.d7690 p = d375896 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7689 p else NetHack.Sokoban22Refined85.d7688 p) = d375896 p
  rw [oldNode7689, oldNode7688]
  rfl
theorem oldNode7691 (p : Pattern) : NetHack.Sokoban22Refined85.d7691 p = d375897 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d7690 p else NetHack.Sokoban22Refined85.d3226 p) = d375897 p
  rw [oldNode7690, oldNode3226]
  rfl
theorem oldNode7692 (p : Pattern) : NetHack.Sokoban22Refined85.d7692 p = d375898 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d3461 p else NetHack.Sokoban22Refined85.d3250 p) = d375898 p
  rw [oldNode3461, oldNode3250]
  rfl
theorem oldNode7693 (p : Pattern) : NetHack.Sokoban22Refined85.d7693 p = d375899 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d3253 p) = d375899 p
  rw [oldNode12, oldNode3253]
  rfl
theorem oldNode7694 (p : Pattern) : NetHack.Sokoban22Refined85.d7694 p = d375900 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7693 p else NetHack.Sokoban22Refined85.d7692 p) = d375900 p
  rw [oldNode7693, oldNode7692]
  rfl
theorem oldNode7695 (p : Pattern) : NetHack.Sokoban22Refined85.d7695 p = d375901 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7694 p) = d375901 p
  rw [oldNode12, oldNode7694]
  rfl
theorem oldNode7696 (p : Pattern) : NetHack.Sokoban22Refined85.d7696 p = d375902 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7695 p else NetHack.Sokoban22Refined85.d7691 p) = d375902 p
  rw [oldNode7695, oldNode7691]
  rfl
theorem oldNode7697 (p : Pattern) : NetHack.Sokoban22Refined85.d7697 p = d375903 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d3279 p) = d375903 p
  rw [oldNode12, oldNode3279]
  rfl
theorem oldNode7698 (p : Pattern) : NetHack.Sokoban22Refined85.d7698 p = d375904 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d7697 p else NetHack.Sokoban22Refined85.d7693 p) = d375904 p
  rw [oldNode7697, oldNode7693]
  rfl
theorem oldNode7699 (p : Pattern) : NetHack.Sokoban22Refined85.d7699 p = d375905 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7698 p) = d375905 p
  rw [oldNode12, oldNode7698]
  rfl
theorem oldNode7700 (p : Pattern) : NetHack.Sokoban22Refined85.d7700 p = d375906 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d7699 p else NetHack.Sokoban22Refined85.d7691 p) = d375906 p
  rw [oldNode7699, oldNode7691]
  rfl
theorem oldNode7701 (p : Pattern) : NetHack.Sokoban22Refined85.d7701 p = d375907 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d7700 p else NetHack.Sokoban22Refined85.d7696 p) = d375907 p
  rw [oldNode7700, oldNode7696]
  rfl
theorem oldNode7702 (p : Pattern) : NetHack.Sokoban22Refined85.d7702 p = d375908 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d3257 p) = d375908 p
  rw [oldNode12, oldNode3257]
  rfl
theorem oldNode7703 (p : Pattern) : NetHack.Sokoban22Refined85.d7703 p = d375909 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d7702 p) = d375909 p
  rw [oldNode12, oldNode7702]
  rfl
end NetHack.Soko22Hazard87
