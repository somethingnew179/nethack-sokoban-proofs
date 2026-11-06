/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes60
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d7320 (p : Pattern) : Int := if p 182 then d7288 p else d7319 p
theorem agree7320 (p q : Pattern) (h : Agree support p q) : d7320 p = d7320 q := by
  simp only [d7320, h 182 (by decide), agree7288 p q h, agree7319 p q h]
theorem nonnegative7320 (p : Pattern) : 0 ≤ d7320 p :=
  nonnegative_ite (p 182) (nonnegative7288 p) (nonnegative7319 p)
def d7321 (p : Pattern) : Int := if p 163 then d12 p else d7320 p
theorem agree7321 (p q : Pattern) (h : Agree support p q) : d7321 p = d7321 q := by
  simp only [d7321, h 163 (by decide), agree12 p q h, agree7320 p q h]
theorem nonnegative7321 (p : Pattern) : 0 ≤ d7321 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7320 p)
def d7322 (p : Pattern) : Int := if p 162 then d7321 p else d7318 p
theorem agree7322 (p q : Pattern) (h : Agree support p q) : d7322 p = d7322 q := by
  simp only [d7322, h 162 (by decide), agree7321 p q h, agree7318 p q h]
theorem nonnegative7322 (p : Pattern) : 0 ≤ d7322 p :=
  nonnegative_ite (p 162) (nonnegative7321 p) (nonnegative7318 p)
def d7323 (p : Pattern) : Int := if p 161 then d7322 p else d7313 p
theorem agree7323 (p q : Pattern) (h : Agree support p q) : d7323 p = d7323 q := by
  simp only [d7323, h 161 (by decide), agree7322 p q h, agree7313 p q h]
theorem nonnegative7323 (p : Pattern) : 0 ≤ d7323 p :=
  nonnegative_ite (p 161) (nonnegative7322 p) (nonnegative7313 p)
def d7324 (p : Pattern) : Int := if p 204 then d7277 p else d2 p
theorem agree7324 (p q : Pattern) (h : Agree support p q) : d7324 p = d7324 q := by
  simp only [d7324, h 204 (by decide), agree7277 p q h, agree2 p q h]
theorem nonnegative7324 (p : Pattern) : 0 ≤ d7324 p :=
  nonnegative_ite (p 204) (nonnegative7277 p) (nonnegative2 p)
def d7325 (p : Pattern) : Int := if p 182 then d12 p else d7324 p
theorem agree7325 (p q : Pattern) (h : Agree support p q) : d7325 p = d7325 q := by
  simp only [d7325, h 182 (by decide), agree12 p q h, agree7324 p q h]
theorem nonnegative7325 (p : Pattern) : 0 ≤ d7325 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7324 p)
def d7326 (p : Pattern) : Int := if p 163 then d7325 p else d7284 p
theorem agree7326 (p q : Pattern) (h : Agree support p q) : d7326 p = d7326 q := by
  simp only [d7326, h 163 (by decide), agree7325 p q h, agree7284 p q h]
theorem nonnegative7326 (p : Pattern) : 0 ≤ d7326 p :=
  nonnegative_ite (p 163) (nonnegative7325 p) (nonnegative7284 p)
def d7327 (p : Pattern) : Int := if p 163 then d7299 p else d7294 p
theorem agree7327 (p q : Pattern) (h : Agree support p q) : d7327 p = d7327 q := by
  simp only [d7327, h 163 (by decide), agree7299 p q h, agree7294 p q h]
theorem nonnegative7327 (p : Pattern) : 0 ≤ d7327 p :=
  nonnegative_ite (p 163) (nonnegative7299 p) (nonnegative7294 p)
def d7328 (p : Pattern) : Int := if p 162 then d7327 p else d7326 p
theorem agree7328 (p q : Pattern) (h : Agree support p q) : d7328 p = d7328 q := by
  simp only [d7328, h 162 (by decide), agree7327 p q h, agree7326 p q h]
theorem nonnegative7328 (p : Pattern) : 0 ≤ d7328 p :=
  nonnegative_ite (p 162) (nonnegative7327 p) (nonnegative7326 p)
def d7329 (p : Pattern) : Int := if p 182 then d12 p else d7315 p
theorem agree7329 (p q : Pattern) (h : Agree support p q) : d7329 p = d7329 q := by
  simp only [d7329, h 182 (by decide), agree12 p q h, agree7315 p q h]
theorem nonnegative7329 (p : Pattern) : 0 ≤ d7329 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7315 p)
def d7330 (p : Pattern) : Int := if p 163 then d7329 p else d7294 p
theorem agree7330 (p q : Pattern) (h : Agree support p q) : d7330 p = d7330 q := by
  simp only [d7330, h 163 (by decide), agree7329 p q h, agree7294 p q h]
theorem nonnegative7330 (p : Pattern) : 0 ≤ d7330 p :=
  nonnegative_ite (p 163) (nonnegative7329 p) (nonnegative7294 p)
def d7331 (p : Pattern) : Int := if p 182 then d12 p else d7319 p
theorem agree7331 (p q : Pattern) (h : Agree support p q) : d7331 p = d7331 q := by
  simp only [d7331, h 182 (by decide), agree12 p q h, agree7319 p q h]
theorem nonnegative7331 (p : Pattern) : 0 ≤ d7331 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7319 p)
def d7332 (p : Pattern) : Int := if p 163 then d12 p else d7331 p
theorem agree7332 (p q : Pattern) (h : Agree support p q) : d7332 p = d7332 q := by
  simp only [d7332, h 163 (by decide), agree12 p q h, agree7331 p q h]
theorem nonnegative7332 (p : Pattern) : 0 ≤ d7332 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7331 p)
def d7333 (p : Pattern) : Int := if p 162 then d7332 p else d7330 p
theorem agree7333 (p q : Pattern) (h : Agree support p q) : d7333 p = d7333 q := by
  simp only [d7333, h 162 (by decide), agree7332 p q h, agree7330 p q h]
theorem nonnegative7333 (p : Pattern) : 0 ≤ d7333 p :=
  nonnegative_ite (p 162) (nonnegative7332 p) (nonnegative7330 p)
def d7334 (p : Pattern) : Int := if p 161 then d7333 p else d7328 p
theorem agree7334 (p q : Pattern) (h : Agree support p q) : d7334 p = d7334 q := by
  simp only [d7334, h 161 (by decide), agree7333 p q h, agree7328 p q h]
theorem nonnegative7334 (p : Pattern) : 0 ≤ d7334 p :=
  nonnegative_ite (p 161) (nonnegative7333 p) (nonnegative7328 p)
def d7335 (p : Pattern) : Int := if p 160 then d7334 p else d7323 p
theorem agree7335 (p q : Pattern) (h : Agree support p q) : d7335 p = d7335 q := by
  simp only [d7335, h 160 (by decide), agree7334 p q h, agree7323 p q h]
theorem nonnegative7335 (p : Pattern) : 0 ≤ d7335 p :=
  nonnegative_ite (p 160) (nonnegative7334 p) (nonnegative7323 p)
def d7336 (p : Pattern) : Int := if p 141 then d7335 p else d7303 p
theorem agree7336 (p q : Pattern) (h : Agree support p q) : d7336 p = d7336 q := by
  simp only [d7336, h 141 (by decide), agree7335 p q h, agree7303 p q h]
theorem nonnegative7336 (p : Pattern) : 0 ≤ d7336 p :=
  nonnegative_ite (p 141) (nonnegative7335 p) (nonnegative7303 p)
def d7337 (p : Pattern) : Int := if p 224 then d7255 p else d7271 p
theorem agree7337 (p q : Pattern) (h : Agree support p q) : d7337 p = d7337 q := by
  simp only [d7337, h 224 (by decide), agree7255 p q h, agree7271 p q h]
theorem nonnegative7337 (p : Pattern) : 0 ≤ d7337 p :=
  nonnegative_ite (p 224) (nonnegative7255 p) (nonnegative7271 p)
def d7338 (p : Pattern) : Int := if p 204 then d7337 p else d0 p
theorem agree7338 (p q : Pattern) (h : Agree support p q) : d7338 p = d7338 q := by
  simp only [d7338, h 204 (by decide), agree7337 p q h, agree0 p q h]
theorem nonnegative7338 (p : Pattern) : 0 ≤ d7338 p :=
  nonnegative_ite (p 204) (nonnegative7337 p) (nonnegative0 p)
def d7339 (p : Pattern) : Int := if p 204 then d12 p else d7246 p
theorem agree7339 (p q : Pattern) (h : Agree support p q) : d7339 p = d7339 q := by
  simp only [d7339, h 204 (by decide), agree12 p q h, agree7246 p q h]
theorem nonnegative7339 (p : Pattern) : 0 ≤ d7339 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7246 p)
def d7340 (p : Pattern) : Int := if p 182 then d7339 p else d7338 p
theorem agree7340 (p q : Pattern) (h : Agree support p q) : d7340 p = d7340 q := by
  simp only [d7340, h 182 (by decide), agree7339 p q h, agree7338 p q h]
theorem nonnegative7340 (p : Pattern) : 0 ≤ d7340 p :=
  nonnegative_ite (p 182) (nonnegative7339 p) (nonnegative7338 p)
def d7341 (p : Pattern) : Int := if p 224 then d7252 p else d7271 p
theorem agree7341 (p q : Pattern) (h : Agree support p q) : d7341 p = d7341 q := by
  simp only [d7341, h 224 (by decide), agree7252 p q h, agree7271 p q h]
theorem nonnegative7341 (p : Pattern) : 0 ≤ d7341 p :=
  nonnegative_ite (p 224) (nonnegative7252 p) (nonnegative7271 p)
def d7342 (p : Pattern) : Int := if p 204 then d12 p else d7341 p
theorem agree7342 (p q : Pattern) (h : Agree support p q) : d7342 p = d7342 q := by
  simp only [d7342, h 204 (by decide), agree12 p q h, agree7341 p q h]
theorem nonnegative7342 (p : Pattern) : 0 ≤ d7342 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7341 p)
def d7343 (p : Pattern) : Int := if p 182 then d7342 p else d7274 p
theorem agree7343 (p q : Pattern) (h : Agree support p q) : d7343 p = d7343 q := by
  simp only [d7343, h 182 (by decide), agree7342 p q h, agree7274 p q h]
theorem nonnegative7343 (p : Pattern) : 0 ≤ d7343 p :=
  nonnegative_ite (p 182) (nonnegative7342 p) (nonnegative7274 p)
def d7344 (p : Pattern) : Int := if p 163 then d7343 p else d7340 p
theorem agree7344 (p q : Pattern) (h : Agree support p q) : d7344 p = d7344 q := by
  simp only [d7344, h 163 (by decide), agree7343 p q h, agree7340 p q h]
theorem nonnegative7344 (p : Pattern) : 0 ≤ d7344 p :=
  nonnegative_ite (p 163) (nonnegative7343 p) (nonnegative7340 p)
def d7345 (p : Pattern) : Int := if p 204 then d12 p else d7273 p
theorem agree7345 (p q : Pattern) (h : Agree support p q) : d7345 p = d7345 q := by
  simp only [d7345, h 204 (by decide), agree12 p q h, agree7273 p q h]
theorem nonnegative7345 (p : Pattern) : 0 ≤ d7345 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7273 p)
def d7346 (p : Pattern) : Int := if p 182 then d7345 p else d7274 p
theorem agree7346 (p q : Pattern) (h : Agree support p q) : d7346 p = d7346 q := by
  simp only [d7346, h 182 (by decide), agree7345 p q h, agree7274 p q h]
theorem nonnegative7346 (p : Pattern) : 0 ≤ d7346 p :=
  nonnegative_ite (p 182) (nonnegative7345 p) (nonnegative7274 p)
def d7347 (p : Pattern) : Int := if p 204 then d12 p else d7292 p
theorem agree7347 (p q : Pattern) (h : Agree support p q) : d7347 p = d7347 q := by
  simp only [d7347, h 204 (by decide), agree12 p q h, agree7292 p q h]
theorem nonnegative7347 (p : Pattern) : 0 ≤ d7347 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7292 p)
def d7348 (p : Pattern) : Int := if p 182 then d7347 p else d7293 p
theorem agree7348 (p q : Pattern) (h : Agree support p q) : d7348 p = d7348 q := by
  simp only [d7348, h 182 (by decide), agree7347 p q h, agree7293 p q h]
theorem nonnegative7348 (p : Pattern) : 0 ≤ d7348 p :=
  nonnegative_ite (p 182) (nonnegative7347 p) (nonnegative7293 p)
def d7349 (p : Pattern) : Int := if p 163 then d7348 p else d7346 p
theorem agree7349 (p q : Pattern) (h : Agree support p q) : d7349 p = d7349 q := by
  simp only [d7349, h 163 (by decide), agree7348 p q h, agree7346 p q h]
theorem nonnegative7349 (p : Pattern) : 0 ≤ d7349 p :=
  nonnegative_ite (p 163) (nonnegative7348 p) (nonnegative7346 p)
def d7350 (p : Pattern) : Int := if p 162 then d7349 p else d7344 p
theorem agree7350 (p q : Pattern) (h : Agree support p q) : d7350 p = d7350 q := by
  simp only [d7350, h 162 (by decide), agree7349 p q h, agree7344 p q h]
theorem nonnegative7350 (p : Pattern) : 0 ≤ d7350 p :=
  nonnegative_ite (p 162) (nonnegative7349 p) (nonnegative7344 p)
def d7351 (p : Pattern) : Int := if p 204 then d12 p else d7262 p
theorem agree7351 (p q : Pattern) (h : Agree support p q) : d7351 p = d7351 q := by
  simp only [d7351, h 204 (by decide), agree12 p q h, agree7262 p q h]
theorem nonnegative7351 (p : Pattern) : 0 ≤ d7351 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7262 p)
def d7352 (p : Pattern) : Int := if p 182 then d7351 p else d7263 p
theorem agree7352 (p q : Pattern) (h : Agree support p q) : d7352 p = d7352 q := by
  simp only [d7352, h 182 (by decide), agree7351 p q h, agree7263 p q h]
theorem nonnegative7352 (p : Pattern) : 0 ≤ d7352 p :=
  nonnegative_ite (p 182) (nonnegative7351 p) (nonnegative7263 p)
def d7353 (p : Pattern) : Int := if p 163 then d12 p else d7352 p
theorem agree7353 (p q : Pattern) (h : Agree support p q) : d7353 p = d7353 q := by
  simp only [d7353, h 163 (by decide), agree12 p q h, agree7352 p q h]
theorem nonnegative7353 (p : Pattern) : 0 ≤ d7353 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7352 p)
def d7354 (p : Pattern) : Int := if p 162 then d7353 p else d7349 p
theorem agree7354 (p q : Pattern) (h : Agree support p q) : d7354 p = d7354 q := by
  simp only [d7354, h 162 (by decide), agree7353 p q h, agree7349 p q h]
theorem nonnegative7354 (p : Pattern) : 0 ≤ d7354 p :=
  nonnegative_ite (p 162) (nonnegative7353 p) (nonnegative7349 p)
def d7355 (p : Pattern) : Int := if p 161 then d7354 p else d7350 p
theorem agree7355 (p q : Pattern) (h : Agree support p q) : d7355 p = d7355 q := by
  simp only [d7355, h 161 (by decide), agree7354 p q h, agree7350 p q h]
theorem nonnegative7355 (p : Pattern) : 0 ≤ d7355 p :=
  nonnegative_ite (p 161) (nonnegative7354 p) (nonnegative7350 p)
def d7356 (p : Pattern) : Int := if p 182 then d7278 p else d7324 p
theorem agree7356 (p q : Pattern) (h : Agree support p q) : d7356 p = d7356 q := by
  simp only [d7356, h 182 (by decide), agree7278 p q h, agree7324 p q h]
theorem nonnegative7356 (p : Pattern) : 0 ≤ d7356 p :=
  nonnegative_ite (p 182) (nonnegative7278 p) (nonnegative7324 p)
def d7357 (p : Pattern) : Int := if p 204 then d7282 p else d6 p
theorem agree7357 (p q : Pattern) (h : Agree support p q) : d7357 p = d7357 q := by
  simp only [d7357, h 204 (by decide), agree7282 p q h, agree6 p q h]
theorem nonnegative7357 (p : Pattern) : 0 ≤ d7357 p :=
  nonnegative_ite (p 204) (nonnegative7282 p) (nonnegative6 p)
def d7358 (p : Pattern) : Int := if p 182 then d7283 p else d7357 p
theorem agree7358 (p q : Pattern) (h : Agree support p q) : d7358 p = d7358 q := by
  simp only [d7358, h 182 (by decide), agree7283 p q h, agree7357 p q h]
theorem nonnegative7358 (p : Pattern) : 0 ≤ d7358 p :=
  nonnegative_ite (p 182) (nonnegative7283 p) (nonnegative7357 p)
def d7359 (p : Pattern) : Int := if p 163 then d7358 p else d7356 p
theorem agree7359 (p q : Pattern) (h : Agree support p q) : d7359 p = d7359 q := by
  simp only [d7359, h 163 (by decide), agree7358 p q h, agree7356 p q h]
theorem nonnegative7359 (p : Pattern) : 0 ≤ d7359 p :=
  nonnegative_ite (p 163) (nonnegative7358 p) (nonnegative7356 p)
def d7360 (p : Pattern) : Int := if p 162 then d7321 p else d7359 p
theorem agree7360 (p q : Pattern) (h : Agree support p q) : d7360 p = d7360 q := by
  simp only [d7360, h 162 (by decide), agree7321 p q h, agree7359 p q h]
theorem nonnegative7360 (p : Pattern) : 0 ≤ d7360 p :=
  nonnegative_ite (p 162) (nonnegative7321 p) (nonnegative7359 p)
def d7361 (p : Pattern) : Int := if p 161 then d12 p else d7360 p
theorem agree7361 (p q : Pattern) (h : Agree support p q) : d7361 p = d7361 q := by
  simp only [d7361, h 161 (by decide), agree12 p q h, agree7360 p q h]
theorem nonnegative7361 (p : Pattern) : 0 ≤ d7361 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7360 p)
def d7362 (p : Pattern) : Int := if p 160 then d7361 p else d7355 p
theorem agree7362 (p q : Pattern) (h : Agree support p q) : d7362 p = d7362 q := by
  simp only [d7362, h 160 (by decide), agree7361 p q h, agree7355 p q h]
theorem nonnegative7362 (p : Pattern) : 0 ≤ d7362 p :=
  nonnegative_ite (p 160) (nonnegative7361 p) (nonnegative7355 p)
def d7363 (p : Pattern) : Int := if p 163 then d7356 p else d7343 p
theorem agree7363 (p q : Pattern) (h : Agree support p q) : d7363 p = d7363 q := by
  simp only [d7363, h 163 (by decide), agree7356 p q h, agree7343 p q h]
theorem nonnegative7363 (p : Pattern) : 0 ≤ d7363 p :=
  nonnegative_ite (p 163) (nonnegative7356 p) (nonnegative7343 p)
def d7364 (p : Pattern) : Int := if p 163 then d7352 p else d7348 p
theorem agree7364 (p q : Pattern) (h : Agree support p q) : d7364 p = d7364 q := by
  simp only [d7364, h 163 (by decide), agree7352 p q h, agree7348 p q h]
theorem nonnegative7364 (p : Pattern) : 0 ≤ d7364 p :=
  nonnegative_ite (p 163) (nonnegative7352 p) (nonnegative7348 p)
def d7365 (p : Pattern) : Int := if p 162 then d7364 p else d7363 p
theorem agree7365 (p q : Pattern) (h : Agree support p q) : d7365 p = d7365 q := by
  simp only [d7365, h 162 (by decide), agree7364 p q h, agree7363 p q h]
theorem nonnegative7365 (p : Pattern) : 0 ≤ d7365 p :=
  nonnegative_ite (p 162) (nonnegative7364 p) (nonnegative7363 p)
def d7366 (p : Pattern) : Int := if p 163 then d7317 p else d7348 p
theorem agree7366 (p q : Pattern) (h : Agree support p q) : d7366 p = d7366 q := by
  simp only [d7366, h 163 (by decide), agree7317 p q h, agree7348 p q h]
theorem nonnegative7366 (p : Pattern) : 0 ≤ d7366 p :=
  nonnegative_ite (p 163) (nonnegative7317 p) (nonnegative7348 p)
def d7367 (p : Pattern) : Int := if p 162 then d7321 p else d7366 p
theorem agree7367 (p q : Pattern) (h : Agree support p q) : d7367 p = d7367 q := by
  simp only [d7367, h 162 (by decide), agree7321 p q h, agree7366 p q h]
theorem nonnegative7367 (p : Pattern) : 0 ≤ d7367 p :=
  nonnegative_ite (p 162) (nonnegative7321 p) (nonnegative7366 p)
def d7368 (p : Pattern) : Int := if p 161 then d7367 p else d7365 p
theorem agree7368 (p q : Pattern) (h : Agree support p q) : d7368 p = d7368 q := by
  simp only [d7368, h 161 (by decide), agree7367 p q h, agree7365 p q h]
theorem nonnegative7368 (p : Pattern) : 0 ≤ d7368 p :=
  nonnegative_ite (p 161) (nonnegative7367 p) (nonnegative7365 p)
def d7369 (p : Pattern) : Int := if p 163 then d12 p else d7358 p
theorem agree7369 (p q : Pattern) (h : Agree support p q) : d7369 p = d7369 q := by
  simp only [d7369, h 163 (by decide), agree12 p q h, agree7358 p q h]
theorem nonnegative7369 (p : Pattern) : 0 ≤ d7369 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7358 p)
def d7370 (p : Pattern) : Int := if p 162 then d12 p else d7369 p
theorem agree7370 (p q : Pattern) (h : Agree support p q) : d7370 p = d7370 q := by
  simp only [d7370, h 162 (by decide), agree12 p q h, agree7369 p q h]
theorem nonnegative7370 (p : Pattern) : 0 ≤ d7370 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7369 p)
def d7371 (p : Pattern) : Int := if p 161 then d12 p else d7370 p
theorem agree7371 (p q : Pattern) (h : Agree support p q) : d7371 p = d7371 q := by
  simp only [d7371, h 161 (by decide), agree12 p q h, agree7370 p q h]
theorem nonnegative7371 (p : Pattern) : 0 ≤ d7371 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7370 p)
def d7372 (p : Pattern) : Int := if p 160 then d7371 p else d7368 p
theorem agree7372 (p q : Pattern) (h : Agree support p q) : d7372 p = d7372 q := by
  simp only [d7372, h 160 (by decide), agree7371 p q h, agree7368 p q h]
theorem nonnegative7372 (p : Pattern) : 0 ≤ d7372 p :=
  nonnegative_ite (p 160) (nonnegative7371 p) (nonnegative7368 p)
def d7373 (p : Pattern) : Int := if p 141 then d7372 p else d7362 p
theorem agree7373 (p q : Pattern) (h : Agree support p q) : d7373 p = d7373 q := by
  simp only [d7373, h 141 (by decide), agree7372 p q h, agree7362 p q h]
theorem nonnegative7373 (p : Pattern) : 0 ≤ d7373 p :=
  nonnegative_ite (p 141) (nonnegative7372 p) (nonnegative7362 p)
def d7374 (p : Pattern) : Int := if p 138 then d7373 p else d7336 p
theorem agree7374 (p q : Pattern) (h : Agree support p q) : d7374 p = d7374 q := by
  simp only [d7374, h 138 (by decide), agree7373 p q h, agree7336 p q h]
theorem nonnegative7374 (p : Pattern) : 0 ≤ d7374 p :=
  nonnegative_ite (p 138) (nonnegative7373 p) (nonnegative7336 p)
def d7375 (p : Pattern) : Int := if p 163 then d7320 p else d7352 p
theorem agree7375 (p q : Pattern) (h : Agree support p q) : d7375 p = d7375 q := by
  simp only [d7375, h 163 (by decide), agree7320 p q h, agree7352 p q h]
theorem nonnegative7375 (p : Pattern) : 0 ≤ d7375 p :=
  nonnegative_ite (p 163) (nonnegative7320 p) (nonnegative7352 p)
def d7376 (p : Pattern) : Int := if p 162 then d7321 p else d7375 p
theorem agree7376 (p q : Pattern) (h : Agree support p q) : d7376 p = d7376 q := by
  simp only [d7376, h 162 (by decide), agree7321 p q h, agree7375 p q h]
theorem nonnegative7376 (p : Pattern) : 0 ≤ d7376 p :=
  nonnegative_ite (p 162) (nonnegative7321 p) (nonnegative7375 p)
def d7377 (p : Pattern) : Int := if p 162 then d12 p else d7321 p
theorem agree7377 (p q : Pattern) (h : Agree support p q) : d7377 p = d7377 q := by
  simp only [d7377, h 162 (by decide), agree12 p q h, agree7321 p q h]
theorem nonnegative7377 (p : Pattern) : 0 ≤ d7377 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7321 p)
def d7378 (p : Pattern) : Int := if p 161 then d7377 p else d7376 p
theorem agree7378 (p q : Pattern) (h : Agree support p q) : d7378 p = d7378 q := by
  simp only [d7378, h 161 (by decide), agree7377 p q h, agree7376 p q h]
theorem nonnegative7378 (p : Pattern) : 0 ≤ d7378 p :=
  nonnegative_ite (p 161) (nonnegative7377 p) (nonnegative7376 p)
def d7379 (p : Pattern) : Int := if p 161 then d12 p else d7377 p
theorem agree7379 (p q : Pattern) (h : Agree support p q) : d7379 p = d7379 q := by
  simp only [d7379, h 161 (by decide), agree12 p q h, agree7377 p q h]
theorem nonnegative7379 (p : Pattern) : 0 ≤ d7379 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7377 p)
def d7380 (p : Pattern) : Int := if p 160 then d7379 p else d7378 p
theorem agree7380 (p q : Pattern) (h : Agree support p q) : d7380 p = d7380 q := by
  simp only [d7380, h 160 (by decide), agree7379 p q h, agree7378 p q h]
theorem nonnegative7380 (p : Pattern) : 0 ≤ d7380 p :=
  nonnegative_ite (p 160) (nonnegative7379 p) (nonnegative7378 p)
def d7381 (p : Pattern) : Int := if p 160 then d12 p else d7379 p
theorem agree7381 (p q : Pattern) (h : Agree support p q) : d7381 p = d7381 q := by
  simp only [d7381, h 160 (by decide), agree12 p q h, agree7379 p q h]
theorem nonnegative7381 (p : Pattern) : 0 ≤ d7381 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative7379 p)
def d7382 (p : Pattern) : Int := if p 141 then d7381 p else d7380 p
theorem agree7382 (p q : Pattern) (h : Agree support p q) : d7382 p = d7382 q := by
  simp only [d7382, h 141 (by decide), agree7381 p q h, agree7380 p q h]
theorem nonnegative7382 (p : Pattern) : 0 ≤ d7382 p :=
  nonnegative_ite (p 141) (nonnegative7381 p) (nonnegative7380 p)
def d7383 (p : Pattern) : Int := if p 138 then d7382 p else d7373 p
theorem agree7383 (p q : Pattern) (h : Agree support p q) : d7383 p = d7383 q := by
  simp only [d7383, h 138 (by decide), agree7382 p q h, agree7373 p q h]
theorem nonnegative7383 (p : Pattern) : 0 ≤ d7383 p :=
  nonnegative_ite (p 138) (nonnegative7382 p) (nonnegative7373 p)
def d7384 (p : Pattern) : Int := if p 116 then d7383 p else d7374 p
theorem agree7384 (p q : Pattern) (h : Agree support p q) : d7384 p = d7384 q := by
  simp only [d7384, h 116 (by decide), agree7383 p q h, agree7374 p q h]
theorem nonnegative7384 (p : Pattern) : 0 ≤ d7384 p :=
  nonnegative_ite (p 116) (nonnegative7383 p) (nonnegative7374 p)
def d7385 (p : Pattern) : Int := if p 138 then d12 p else d7373 p
theorem agree7385 (p q : Pattern) (h : Agree support p q) : d7385 p = d7385 q := by
  simp only [d7385, h 138 (by decide), agree12 p q h, agree7373 p q h]
theorem nonnegative7385 (p : Pattern) : 0 ≤ d7385 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7373 p)
def d7386 (p : Pattern) : Int := if p 116 then d7385 p else d7374 p
theorem agree7386 (p q : Pattern) (h : Agree support p q) : d7386 p = d7386 q := by
  simp only [d7386, h 116 (by decide), agree7385 p q h, agree7374 p q h]
theorem nonnegative7386 (p : Pattern) : 0 ≤ d7386 p :=
  nonnegative_ite (p 116) (nonnegative7385 p) (nonnegative7374 p)
def d7387 (p : Pattern) : Int := if p 115 then d7386 p else d7384 p
theorem agree7387 (p q : Pattern) (h : Agree support p q) : d7387 p = d7387 q := by
  simp only [d7387, h 115 (by decide), agree7386 p q h, agree7384 p q h]
theorem nonnegative7387 (p : Pattern) : 0 ≤ d7387 p :=
  nonnegative_ite (p 115) (nonnegative7386 p) (nonnegative7384 p)
def d7388 (p : Pattern) : Int := if p 225 then d5 p else d1 p
theorem agree7388 (p q : Pattern) (h : Agree support p q) : d7388 p = d7388 q := by
  simp only [d7388, h 225 (by decide), agree5 p q h, agree1 p q h]
theorem nonnegative7388 (p : Pattern) : 0 ≤ d7388 p :=
  nonnegative_ite (p 225) (nonnegative5 p) (nonnegative1 p)
def d7389 (p : Pattern) : Int := if p 224 then d5 p else d7388 p
theorem agree7389 (p q : Pattern) (h : Agree support p q) : d7389 p = d7389 q := by
  simp only [d7389, h 224 (by decide), agree5 p q h, agree7388 p q h]
theorem nonnegative7389 (p : Pattern) : 0 ≤ d7389 p :=
  nonnegative_ite (p 224) (nonnegative5 p) (nonnegative7388 p)
def d7390 (p : Pattern) : Int := if p 204 then d7389 p else d1 p
theorem agree7390 (p q : Pattern) (h : Agree support p q) : d7390 p = d7390 q := by
  simp only [d7390, h 204 (by decide), agree7389 p q h, agree1 p q h]
theorem nonnegative7390 (p : Pattern) : 0 ≤ d7390 p :=
  nonnegative_ite (p 204) (nonnegative7389 p) (nonnegative1 p)
def d7391 (p : Pattern) : Int := if p 225 then d3 p else d1 p
theorem agree7391 (p q : Pattern) (h : Agree support p q) : d7391 p = d7391 q := by
  simp only [d7391, h 225 (by decide), agree3 p q h, agree1 p q h]
theorem nonnegative7391 (p : Pattern) : 0 ≤ d7391 p :=
  nonnegative_ite (p 225) (nonnegative3 p) (nonnegative1 p)
def d7392 (p : Pattern) : Int := if p 224 then d3 p else d7391 p
theorem agree7392 (p q : Pattern) (h : Agree support p q) : d7392 p = d7392 q := by
  simp only [d7392, h 224 (by decide), agree3 p q h, agree7391 p q h]
theorem nonnegative7392 (p : Pattern) : 0 ≤ d7392 p :=
  nonnegative_ite (p 224) (nonnegative3 p) (nonnegative7391 p)
def d7393 (p : Pattern) : Int := if p 204 then d12 p else d7392 p
theorem agree7393 (p q : Pattern) (h : Agree support p q) : d7393 p = d7393 q := by
  simp only [d7393, h 204 (by decide), agree12 p q h, agree7392 p q h]
theorem nonnegative7393 (p : Pattern) : 0 ≤ d7393 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7392 p)
def d7394 (p : Pattern) : Int := if p 182 then d7393 p else d7390 p
theorem agree7394 (p q : Pattern) (h : Agree support p q) : d7394 p = d7394 q := by
  simp only [d7394, h 182 (by decide), agree7393 p q h, agree7390 p q h]
theorem nonnegative7394 (p : Pattern) : 0 ≤ d7394 p :=
  nonnegative_ite (p 182) (nonnegative7393 p) (nonnegative7390 p)
def d7395 (p : Pattern) : Int := if p 225 then d9 p else d5 p
theorem agree7395 (p q : Pattern) (h : Agree support p q) : d7395 p = d7395 q := by
  simp only [d7395, h 225 (by decide), agree9 p q h, agree5 p q h]
theorem nonnegative7395 (p : Pattern) : 0 ≤ d7395 p :=
  nonnegative_ite (p 225) (nonnegative9 p) (nonnegative5 p)
def d7396 (p : Pattern) : Int := if p 224 then d9 p else d7395 p
theorem agree7396 (p q : Pattern) (h : Agree support p q) : d7396 p = d7396 q := by
  simp only [d7396, h 224 (by decide), agree9 p q h, agree7395 p q h]
theorem nonnegative7396 (p : Pattern) : 0 ≤ d7396 p :=
  nonnegative_ite (p 224) (nonnegative9 p) (nonnegative7395 p)
def d7397 (p : Pattern) : Int := if p 204 then d7396 p else d5 p
theorem agree7397 (p q : Pattern) (h : Agree support p q) : d7397 p = d7397 q := by
  simp only [d7397, h 204 (by decide), agree7396 p q h, agree5 p q h]
theorem nonnegative7397 (p : Pattern) : 0 ≤ d7397 p :=
  nonnegative_ite (p 204) (nonnegative7396 p) (nonnegative5 p)
def d7398 (p : Pattern) : Int := if p 225 then d7 p else d5 p
theorem agree7398 (p q : Pattern) (h : Agree support p q) : d7398 p = d7398 q := by
  simp only [d7398, h 225 (by decide), agree7 p q h, agree5 p q h]
theorem nonnegative7398 (p : Pattern) : 0 ≤ d7398 p :=
  nonnegative_ite (p 225) (nonnegative7 p) (nonnegative5 p)
def d7399 (p : Pattern) : Int := if p 224 then d7 p else d7398 p
theorem agree7399 (p q : Pattern) (h : Agree support p q) : d7399 p = d7399 q := by
  simp only [d7399, h 224 (by decide), agree7 p q h, agree7398 p q h]
theorem nonnegative7399 (p : Pattern) : 0 ≤ d7399 p :=
  nonnegative_ite (p 224) (nonnegative7 p) (nonnegative7398 p)
def d7400 (p : Pattern) : Int := if p 204 then d12 p else d7399 p
theorem agree7400 (p q : Pattern) (h : Agree support p q) : d7400 p = d7400 q := by
  simp only [d7400, h 204 (by decide), agree12 p q h, agree7399 p q h]
theorem nonnegative7400 (p : Pattern) : 0 ≤ d7400 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7399 p)
def d7401 (p : Pattern) : Int := if p 182 then d7400 p else d7397 p
theorem agree7401 (p q : Pattern) (h : Agree support p q) : d7401 p = d7401 q := by
  simp only [d7401, h 182 (by decide), agree7400 p q h, agree7397 p q h]
theorem nonnegative7401 (p : Pattern) : 0 ≤ d7401 p :=
  nonnegative_ite (p 182) (nonnegative7400 p) (nonnegative7397 p)
def d7402 (p : Pattern) : Int := if p 163 then d7401 p else d7394 p
theorem agree7402 (p q : Pattern) (h : Agree support p q) : d7402 p = d7402 q := by
  simp only [d7402, h 163 (by decide), agree7401 p q h, agree7394 p q h]
theorem nonnegative7402 (p : Pattern) : 0 ≤ d7402 p :=
  nonnegative_ite (p 163) (nonnegative7401 p) (nonnegative7394 p)
def d7403 (p : Pattern) : Int := if p 162 then d7402 p else d7394 p
theorem agree7403 (p q : Pattern) (h : Agree support p q) : d7403 p = d7403 q := by
  simp only [d7403, h 162 (by decide), agree7402 p q h, agree7394 p q h]
theorem nonnegative7403 (p : Pattern) : 0 ≤ d7403 p :=
  nonnegative_ite (p 162) (nonnegative7402 p) (nonnegative7394 p)
def d7404 (p : Pattern) : Int := if p 163 then d12 p else d7317 p
theorem agree7404 (p q : Pattern) (h : Agree support p q) : d7404 p = d7404 q := by
  simp only [d7404, h 163 (by decide), agree12 p q h, agree7317 p q h]
theorem nonnegative7404 (p : Pattern) : 0 ≤ d7404 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7317 p)
def d7405 (p : Pattern) : Int := if p 162 then d7404 p else d7402 p
theorem agree7405 (p q : Pattern) (h : Agree support p q) : d7405 p = d7405 q := by
  simp only [d7405, h 162 (by decide), agree7404 p q h, agree7402 p q h]
theorem nonnegative7405 (p : Pattern) : 0 ≤ d7405 p :=
  nonnegative_ite (p 162) (nonnegative7404 p) (nonnegative7402 p)
def d7406 (p : Pattern) : Int := if p 161 then d7405 p else d7403 p
theorem agree7406 (p q : Pattern) (h : Agree support p q) : d7406 p = d7406 q := by
  simp only [d7406, h 161 (by decide), agree7405 p q h, agree7403 p q h]
theorem nonnegative7406 (p : Pattern) : 0 ≤ d7406 p :=
  nonnegative_ite (p 161) (nonnegative7405 p) (nonnegative7403 p)
def d7407 (p : Pattern) : Int := if p 225 then d7 p else d1 p
theorem agree7407 (p q : Pattern) (h : Agree support p q) : d7407 p = d7407 q := by
  simp only [d7407, h 225 (by decide), agree7 p q h, agree1 p q h]
theorem nonnegative7407 (p : Pattern) : 0 ≤ d7407 p :=
  nonnegative_ite (p 225) (nonnegative7 p) (nonnegative1 p)
def d7408 (p : Pattern) : Int := if p 225 then d10 p else d5 p
theorem agree7408 (p q : Pattern) (h : Agree support p q) : d7408 p = d7408 q := by
  simp only [d7408, h 225 (by decide), agree10 p q h, agree5 p q h]
theorem nonnegative7408 (p : Pattern) : 0 ≤ d7408 p :=
  nonnegative_ite (p 225) (nonnegative10 p) (nonnegative5 p)
def d7409 (p : Pattern) : Int := if p 224 then d7408 p else d7407 p
theorem agree7409 (p q : Pattern) (h : Agree support p q) : d7409 p = d7409 q := by
  simp only [d7409, h 224 (by decide), agree7408 p q h, agree7407 p q h]
theorem nonnegative7409 (p : Pattern) : 0 ≤ d7409 p :=
  nonnegative_ite (p 224) (nonnegative7408 p) (nonnegative7407 p)
def d7410 (p : Pattern) : Int := if p 204 then d7409 p else d1 p
theorem agree7410 (p q : Pattern) (h : Agree support p q) : d7410 p = d7410 q := by
  simp only [d7410, h 204 (by decide), agree7409 p q h, agree1 p q h]
theorem nonnegative7410 (p : Pattern) : 0 ≤ d7410 p :=
  nonnegative_ite (p 204) (nonnegative7409 p) (nonnegative1 p)
def d7411 (p : Pattern) : Int := if p 225 then d9 p else d3 p
theorem agree7411 (p q : Pattern) (h : Agree support p q) : d7411 p = d7411 q := by
  simp only [d7411, h 225 (by decide), agree9 p q h, agree3 p q h]
theorem nonnegative7411 (p : Pattern) : 0 ≤ d7411 p :=
  nonnegative_ite (p 225) (nonnegative9 p) (nonnegative3 p)
def d7412 (p : Pattern) : Int := if p 225 then d12 p else d7 p
theorem agree7412 (p q : Pattern) (h : Agree support p q) : d7412 p = d7412 q := by
  simp only [d7412, h 225 (by decide), agree12 p q h, agree7 p q h]
theorem nonnegative7412 (p : Pattern) : 0 ≤ d7412 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative7 p)
def d7413 (p : Pattern) : Int := if p 224 then d7412 p else d7411 p
theorem agree7413 (p q : Pattern) (h : Agree support p q) : d7413 p = d7413 q := by
  simp only [d7413, h 224 (by decide), agree7412 p q h, agree7411 p q h]
theorem nonnegative7413 (p : Pattern) : 0 ≤ d7413 p :=
  nonnegative_ite (p 224) (nonnegative7412 p) (nonnegative7411 p)
def d7414 (p : Pattern) : Int := if p 204 then d12 p else d7413 p
theorem agree7414 (p q : Pattern) (h : Agree support p q) : d7414 p = d7414 q := by
  simp only [d7414, h 204 (by decide), agree12 p q h, agree7413 p q h]
theorem nonnegative7414 (p : Pattern) : 0 ≤ d7414 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7413 p)
def d7415 (p : Pattern) : Int := if p 182 then d7414 p else d7410 p
theorem agree7415 (p q : Pattern) (h : Agree support p q) : d7415 p = d7415 q := by
  simp only [d7415, h 182 (by decide), agree7414 p q h, agree7410 p q h]
theorem nonnegative7415 (p : Pattern) : 0 ≤ d7415 p :=
  nonnegative_ite (p 182) (nonnegative7414 p) (nonnegative7410 p)
def d7416 (p : Pattern) : Int := if p 224 then d7286 p else d7412 p
theorem agree7416 (p q : Pattern) (h : Agree support p q) : d7416 p = d7416 q := by
  simp only [d7416, h 224 (by decide), agree7286 p q h, agree7412 p q h]
theorem nonnegative7416 (p : Pattern) : 0 ≤ d7416 p :=
  nonnegative_ite (p 224) (nonnegative7286 p) (nonnegative7412 p)
def d7417 (p : Pattern) : Int := if p 204 then d12 p else d7416 p
theorem agree7417 (p q : Pattern) (h : Agree support p q) : d7417 p = d7417 q := by
  simp only [d7417, h 204 (by decide), agree12 p q h, agree7416 p q h]
theorem nonnegative7417 (p : Pattern) : 0 ≤ d7417 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7416 p)
def d7418 (p : Pattern) : Int := if p 182 then d7417 p else d7410 p
theorem agree7418 (p q : Pattern) (h : Agree support p q) : d7418 p = d7418 q := by
  simp only [d7418, h 182 (by decide), agree7417 p q h, agree7410 p q h]
theorem nonnegative7418 (p : Pattern) : 0 ≤ d7418 p :=
  nonnegative_ite (p 182) (nonnegative7417 p) (nonnegative7410 p)
def d7419 (p : Pattern) : Int := if p 163 then d7418 p else d7415 p
theorem agree7419 (p q : Pattern) (h : Agree support p q) : d7419 p = d7419 q := by
  simp only [d7419, h 163 (by decide), agree7418 p q h, agree7415 p q h]
theorem nonnegative7419 (p : Pattern) : 0 ≤ d7419 p :=
  nonnegative_ite (p 163) (nonnegative7418 p) (nonnegative7415 p)
def d7420 (p : Pattern) : Int := if p 182 then d12 p else d7410 p
theorem agree7420 (p q : Pattern) (h : Agree support p q) : d7420 p = d7420 q := by
  simp only [d7420, h 182 (by decide), agree12 p q h, agree7410 p q h]
theorem nonnegative7420 (p : Pattern) : 0 ≤ d7420 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7410 p)
def d7421 (p : Pattern) : Int := if p 225 then d11 p else d5 p
theorem agree7421 (p q : Pattern) (h : Agree support p q) : d7421 p = d7421 q := by
  simp only [d7421, h 225 (by decide), agree11 p q h, agree5 p q h]
theorem nonnegative7421 (p : Pattern) : 0 ≤ d7421 p :=
  nonnegative_ite (p 225) (nonnegative11 p) (nonnegative5 p)
def d7422 (p : Pattern) : Int := if p 224 then d7261 p else d7421 p
theorem agree7422 (p q : Pattern) (h : Agree support p q) : d7422 p = d7422 q := by
  simp only [d7422, h 224 (by decide), agree7261 p q h, agree7421 p q h]
theorem nonnegative7422 (p : Pattern) : 0 ≤ d7422 p :=
  nonnegative_ite (p 224) (nonnegative7261 p) (nonnegative7421 p)
def d7423 (p : Pattern) : Int := if p 204 then d7422 p else d5 p
theorem agree7423 (p q : Pattern) (h : Agree support p q) : d7423 p = d7423 q := by
  simp only [d7423, h 204 (by decide), agree7422 p q h, agree5 p q h]
theorem nonnegative7423 (p : Pattern) : 0 ≤ d7423 p :=
  nonnegative_ite (p 204) (nonnegative7422 p) (nonnegative5 p)
def d7424 (p : Pattern) : Int := if p 182 then d12 p else d7423 p
theorem agree7424 (p q : Pattern) (h : Agree support p q) : d7424 p = d7424 q := by
  simp only [d7424, h 182 (by decide), agree12 p q h, agree7423 p q h]
theorem nonnegative7424 (p : Pattern) : 0 ≤ d7424 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7423 p)
def d7425 (p : Pattern) : Int := if p 163 then d7424 p else d7420 p
theorem agree7425 (p q : Pattern) (h : Agree support p q) : d7425 p = d7425 q := by
  simp only [d7425, h 163 (by decide), agree7424 p q h, agree7420 p q h]
theorem nonnegative7425 (p : Pattern) : 0 ≤ d7425 p :=
  nonnegative_ite (p 163) (nonnegative7424 p) (nonnegative7420 p)
def d7426 (p : Pattern) : Int := if p 162 then d7425 p else d7419 p
theorem agree7426 (p q : Pattern) (h : Agree support p q) : d7426 p = d7426 q := by
  simp only [d7426, h 162 (by decide), agree7425 p q h, agree7419 p q h]
theorem nonnegative7426 (p : Pattern) : 0 ≤ d7426 p :=
  nonnegative_ite (p 162) (nonnegative7425 p) (nonnegative7419 p)
def d7427 (p : Pattern) : Int := if p 163 then d12 p else d7329 p
theorem agree7427 (p q : Pattern) (h : Agree support p q) : d7427 p = d7427 q := by
  simp only [d7427, h 163 (by decide), agree12 p q h, agree7329 p q h]
theorem nonnegative7427 (p : Pattern) : 0 ≤ d7427 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7329 p)
def d7428 (p : Pattern) : Int := if p 162 then d7427 p else d7425 p
theorem agree7428 (p q : Pattern) (h : Agree support p q) : d7428 p = d7428 q := by
  simp only [d7428, h 162 (by decide), agree7427 p q h, agree7425 p q h]
theorem nonnegative7428 (p : Pattern) : 0 ≤ d7428 p :=
  nonnegative_ite (p 162) (nonnegative7427 p) (nonnegative7425 p)
def d7429 (p : Pattern) : Int := if p 161 then d7428 p else d7426 p
theorem agree7429 (p q : Pattern) (h : Agree support p q) : d7429 p = d7429 q := by
  simp only [d7429, h 161 (by decide), agree7428 p q h, agree7426 p q h]
theorem nonnegative7429 (p : Pattern) : 0 ≤ d7429 p :=
  nonnegative_ite (p 161) (nonnegative7428 p) (nonnegative7426 p)
def d7430 (p : Pattern) : Int := if p 160 then d7429 p else d7406 p
theorem agree7430 (p q : Pattern) (h : Agree support p q) : d7430 p = d7430 q := by
  simp only [d7430, h 160 (by decide), agree7429 p q h, agree7406 p q h]
theorem nonnegative7430 (p : Pattern) : 0 ≤ d7430 p :=
  nonnegative_ite (p 160) (nonnegative7429 p) (nonnegative7406 p)
def d7431 (p : Pattern) : Int := if p 225 then d7 p else d3 p
theorem agree7431 (p q : Pattern) (h : Agree support p q) : d7431 p = d7431 q := by
  simp only [d7431, h 225 (by decide), agree7 p q h, agree3 p q h]
theorem nonnegative7431 (p : Pattern) : 0 ≤ d7431 p :=
  nonnegative_ite (p 225) (nonnegative7 p) (nonnegative3 p)
def d7432 (p : Pattern) : Int := if p 224 then d7 p else d7431 p
theorem agree7432 (p q : Pattern) (h : Agree support p q) : d7432 p = d7432 q := by
  simp only [d7432, h 224 (by decide), agree7 p q h, agree7431 p q h]
theorem nonnegative7432 (p : Pattern) : 0 ≤ d7432 p :=
  nonnegative_ite (p 224) (nonnegative7 p) (nonnegative7431 p)
def d7433 (p : Pattern) : Int := if p 204 then d7432 p else d3 p
theorem agree7433 (p q : Pattern) (h : Agree support p q) : d7433 p = d7433 q := by
  simp only [d7433, h 204 (by decide), agree7432 p q h, agree3 p q h]
theorem nonnegative7433 (p : Pattern) : 0 ≤ d7433 p :=
  nonnegative_ite (p 204) (nonnegative7432 p) (nonnegative3 p)
def d7434 (p : Pattern) : Int := if p 225 then d5 p else d3 p
theorem agree7434 (p q : Pattern) (h : Agree support p q) : d7434 p = d7434 q := by
  simp only [d7434, h 225 (by decide), agree5 p q h, agree3 p q h]
theorem nonnegative7434 (p : Pattern) : 0 ≤ d7434 p :=
  nonnegative_ite (p 225) (nonnegative5 p) (nonnegative3 p)
def d7435 (p : Pattern) : Int := if p 224 then d5 p else d7434 p
theorem agree7435 (p q : Pattern) (h : Agree support p q) : d7435 p = d7435 q := by
  simp only [d7435, h 224 (by decide), agree5 p q h, agree7434 p q h]
theorem nonnegative7435 (p : Pattern) : 0 ≤ d7435 p :=
  nonnegative_ite (p 224) (nonnegative5 p) (nonnegative7434 p)
def d7436 (p : Pattern) : Int := if p 204 then d12 p else d7435 p
theorem agree7436 (p q : Pattern) (h : Agree support p q) : d7436 p = d7436 q := by
  simp only [d7436, h 204 (by decide), agree12 p q h, agree7435 p q h]
theorem nonnegative7436 (p : Pattern) : 0 ≤ d7436 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7435 p)
def d7437 (p : Pattern) : Int := if p 182 then d7436 p else d7433 p
theorem agree7437 (p q : Pattern) (h : Agree support p q) : d7437 p = d7437 q := by
  simp only [d7437, h 182 (by decide), agree7436 p q h, agree7433 p q h]
theorem nonnegative7437 (p : Pattern) : 0 ≤ d7437 p :=
  nonnegative_ite (p 182) (nonnegative7436 p) (nonnegative7433 p)
def d7438 (p : Pattern) : Int := if p 163 then d7437 p else d7394 p
theorem agree7438 (p q : Pattern) (h : Agree support p q) : d7438 p = d7438 q := by
  simp only [d7438, h 163 (by decide), agree7437 p q h, agree7394 p q h]
theorem nonnegative7438 (p : Pattern) : 0 ≤ d7438 p :=
  nonnegative_ite (p 163) (nonnegative7437 p) (nonnegative7394 p)
def d7439 (p : Pattern) : Int := if p 163 then d7317 p else d7401 p
theorem agree7439 (p q : Pattern) (h : Agree support p q) : d7439 p = d7439 q := by
  simp only [d7439, h 163 (by decide), agree7317 p q h, agree7401 p q h]
theorem nonnegative7439 (p : Pattern) : 0 ≤ d7439 p :=
  nonnegative_ite (p 163) (nonnegative7317 p) (nonnegative7401 p)
end NetHack.Sokoban22Refined85
