/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes35
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d4320 (p : Pattern) : Int := if p 160 then d4319 p else d4306 p
theorem agree4320 (p q : Pattern) (h : Agree support p q) : d4320 p = d4320 q := by
  simp only [d4320, h 160 (by decide), agree4319 p q h, agree4306 p q h]
theorem nonnegative4320 (p : Pattern) : 0 ≤ d4320 p :=
  nonnegative_ite (p 160) (nonnegative4319 p) (nonnegative4306 p)
def d4321 (p : Pattern) : Int := if p 160 then d969 p else d4313 p
theorem agree4321 (p q : Pattern) (h : Agree support p q) : d4321 p = d4321 q := by
  simp only [d4321, h 160 (by decide), agree969 p q h, agree4313 p q h]
theorem nonnegative4321 (p : Pattern) : 0 ≤ d4321 p :=
  nonnegative_ite (p 160) (nonnegative969 p) (nonnegative4313 p)
def d4322 (p : Pattern) : Int := if p 141 then d4321 p else d4320 p
theorem agree4322 (p q : Pattern) (h : Agree support p q) : d4322 p = d4322 q := by
  simp only [d4322, h 141 (by decide), agree4321 p q h, agree4320 p q h]
theorem nonnegative4322 (p : Pattern) : 0 ≤ d4322 p :=
  nonnegative_ite (p 141) (nonnegative4321 p) (nonnegative4320 p)
def d4323 (p : Pattern) : Int := if p 138 then d4322 p else d4318 p
theorem agree4323 (p q : Pattern) (h : Agree support p q) : d4323 p = d4323 q := by
  simp only [d4323, h 138 (by decide), agree4322 p q h, agree4318 p q h]
theorem nonnegative4323 (p : Pattern) : 0 ≤ d4323 p :=
  nonnegative_ite (p 138) (nonnegative4322 p) (nonnegative4318 p)
def d4324 (p : Pattern) : Int := if p 162 then d62 p else d26 p
theorem agree4324 (p q : Pattern) (h : Agree support p q) : d4324 p = d4324 q := by
  simp only [d4324, h 162 (by decide), agree62 p q h, agree26 p q h]
theorem nonnegative4324 (p : Pattern) : 0 ≤ d4324 p :=
  nonnegative_ite (p 162) (nonnegative62 p) (nonnegative26 p)
def d4325 (p : Pattern) : Int := if p 161 then d4160 p else d4324 p
theorem agree4325 (p q : Pattern) (h : Agree support p q) : d4325 p = d4325 q := by
  simp only [d4325, h 161 (by decide), agree4160 p q h, agree4324 p q h]
theorem nonnegative4325 (p : Pattern) : 0 ≤ d4325 p :=
  nonnegative_ite (p 161) (nonnegative4160 p) (nonnegative4324 p)
def d4326 (p : Pattern) : Int := if p 160 then d4161 p else d4325 p
theorem agree4326 (p q : Pattern) (h : Agree support p q) : d4326 p = d4326 q := by
  simp only [d4326, h 160 (by decide), agree4161 p q h, agree4325 p q h]
theorem nonnegative4326 (p : Pattern) : 0 ≤ d4326 p :=
  nonnegative_ite (p 160) (nonnegative4161 p) (nonnegative4325 p)
def d4327 (p : Pattern) : Int := if p 141 then d4162 p else d4326 p
theorem agree4327 (p q : Pattern) (h : Agree support p q) : d4327 p = d4327 q := by
  simp only [d4327, h 141 (by decide), agree4162 p q h, agree4326 p q h]
theorem nonnegative4327 (p : Pattern) : 0 ≤ d4327 p :=
  nonnegative_ite (p 141) (nonnegative4162 p) (nonnegative4326 p)
def d4328 (p : Pattern) : Int := if p 138 then d4327 p else d4322 p
theorem agree4328 (p q : Pattern) (h : Agree support p q) : d4328 p = d4328 q := by
  simp only [d4328, h 138 (by decide), agree4327 p q h, agree4322 p q h]
theorem nonnegative4328 (p : Pattern) : 0 ≤ d4328 p :=
  nonnegative_ite (p 138) (nonnegative4327 p) (nonnegative4322 p)
def d4329 (p : Pattern) : Int := if p 116 then d4328 p else d4323 p
theorem agree4329 (p q : Pattern) (h : Agree support p q) : d4329 p = d4329 q := by
  simp only [d4329, h 116 (by decide), agree4328 p q h, agree4323 p q h]
theorem nonnegative4329 (p : Pattern) : 0 ≤ d4329 p :=
  nonnegative_ite (p 116) (nonnegative4328 p) (nonnegative4323 p)
def d4330 (p : Pattern) : Int := if p 138 then d12 p else d4322 p
theorem agree4330 (p q : Pattern) (h : Agree support p q) : d4330 p = d4330 q := by
  simp only [d4330, h 138 (by decide), agree12 p q h, agree4322 p q h]
theorem nonnegative4330 (p : Pattern) : 0 ≤ d4330 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4322 p)
def d4331 (p : Pattern) : Int := if p 116 then d4330 p else d4323 p
theorem agree4331 (p q : Pattern) (h : Agree support p q) : d4331 p = d4331 q := by
  simp only [d4331, h 116 (by decide), agree4330 p q h, agree4323 p q h]
theorem nonnegative4331 (p : Pattern) : 0 ≤ d4331 p :=
  nonnegative_ite (p 116) (nonnegative4330 p) (nonnegative4323 p)
def d4332 (p : Pattern) : Int := if p 115 then d4331 p else d4329 p
theorem agree4332 (p q : Pattern) (h : Agree support p q) : d4332 p = d4332 q := by
  simp only [d4332, h 115 (by decide), agree4331 p q h, agree4329 p q h]
theorem nonnegative4332 (p : Pattern) : 0 ≤ d4332 p :=
  nonnegative_ite (p 115) (nonnegative4331 p) (nonnegative4329 p)
def d4333 (p : Pattern) : Int := if p 162 then d60 p else d105 p
theorem agree4333 (p q : Pattern) (h : Agree support p q) : d4333 p = d4333 q := by
  simp only [d4333, h 162 (by decide), agree60 p q h, agree105 p q h]
theorem nonnegative4333 (p : Pattern) : 0 ≤ d4333 p :=
  nonnegative_ite (p 162) (nonnegative60 p) (nonnegative105 p)
def d4334 (p : Pattern) : Int := if p 161 then d4333 p else d105 p
theorem agree4334 (p q : Pattern) (h : Agree support p q) : d4334 p = d4334 q := by
  simp only [d4334, h 161 (by decide), agree4333 p q h, agree105 p q h]
theorem nonnegative4334 (p : Pattern) : 0 ≤ d4334 p :=
  nonnegative_ite (p 161) (nonnegative4333 p) (nonnegative105 p)
def d4335 (p : Pattern) : Int := if p 162 then d124 p else d118 p
theorem agree4335 (p q : Pattern) (h : Agree support p q) : d4335 p = d4335 q := by
  simp only [d4335, h 162 (by decide), agree124 p q h, agree118 p q h]
theorem nonnegative4335 (p : Pattern) : 0 ≤ d4335 p :=
  nonnegative_ite (p 162) (nonnegative124 p) (nonnegative118 p)
def d4336 (p : Pattern) : Int := if p 162 then d70 p else d124 p
theorem agree4336 (p q : Pattern) (h : Agree support p q) : d4336 p = d4336 q := by
  simp only [d4336, h 162 (by decide), agree70 p q h, agree124 p q h]
theorem nonnegative4336 (p : Pattern) : 0 ≤ d4336 p :=
  nonnegative_ite (p 162) (nonnegative70 p) (nonnegative124 p)
def d4337 (p : Pattern) : Int := if p 161 then d4336 p else d4335 p
theorem agree4337 (p q : Pattern) (h : Agree support p q) : d4337 p = d4337 q := by
  simp only [d4337, h 161 (by decide), agree4336 p q h, agree4335 p q h]
theorem nonnegative4337 (p : Pattern) : 0 ≤ d4337 p :=
  nonnegative_ite (p 161) (nonnegative4336 p) (nonnegative4335 p)
def d4338 (p : Pattern) : Int := if p 160 then d4337 p else d4334 p
theorem agree4338 (p q : Pattern) (h : Agree support p q) : d4338 p = d4338 q := by
  simp only [d4338, h 160 (by decide), agree4337 p q h, agree4334 p q h]
theorem nonnegative4338 (p : Pattern) : 0 ≤ d4338 p :=
  nonnegative_ite (p 160) (nonnegative4337 p) (nonnegative4334 p)
def d4339 (p : Pattern) : Int := if p 162 then d132 p else d105 p
theorem agree4339 (p q : Pattern) (h : Agree support p q) : d4339 p = d4339 q := by
  simp only [d4339, h 162 (by decide), agree132 p q h, agree105 p q h]
theorem nonnegative4339 (p : Pattern) : 0 ≤ d4339 p :=
  nonnegative_ite (p 162) (nonnegative132 p) (nonnegative105 p)
def d4340 (p : Pattern) : Int := if p 161 then d1061 p else d4339 p
theorem agree4340 (p q : Pattern) (h : Agree support p q) : d4340 p = d4340 q := by
  simp only [d4340, h 161 (by decide), agree1061 p q h, agree4339 p q h]
theorem nonnegative4340 (p : Pattern) : 0 ≤ d4340 p :=
  nonnegative_ite (p 161) (nonnegative1061 p) (nonnegative4339 p)
def d4341 (p : Pattern) : Int := if p 162 then d139 p else d132 p
theorem agree4341 (p q : Pattern) (h : Agree support p q) : d4341 p = d4341 q := by
  simp only [d4341, h 162 (by decide), agree139 p q h, agree132 p q h]
theorem nonnegative4341 (p : Pattern) : 0 ≤ d4341 p :=
  nonnegative_ite (p 162) (nonnegative139 p) (nonnegative132 p)
def d4342 (p : Pattern) : Int := if p 162 then d12 p else d139 p
theorem agree4342 (p q : Pattern) (h : Agree support p q) : d4342 p = d4342 q := by
  simp only [d4342, h 162 (by decide), agree12 p q h, agree139 p q h]
theorem nonnegative4342 (p : Pattern) : 0 ≤ d4342 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative139 p)
def d4343 (p : Pattern) : Int := if p 161 then d4342 p else d4341 p
theorem agree4343 (p q : Pattern) (h : Agree support p q) : d4343 p = d4343 q := by
  simp only [d4343, h 161 (by decide), agree4342 p q h, agree4341 p q h]
theorem nonnegative4343 (p : Pattern) : 0 ≤ d4343 p :=
  nonnegative_ite (p 161) (nonnegative4342 p) (nonnegative4341 p)
def d4344 (p : Pattern) : Int := if p 160 then d4343 p else d4340 p
theorem agree4344 (p q : Pattern) (h : Agree support p q) : d4344 p = d4344 q := by
  simp only [d4344, h 160 (by decide), agree4343 p q h, agree4340 p q h]
theorem nonnegative4344 (p : Pattern) : 0 ≤ d4344 p :=
  nonnegative_ite (p 160) (nonnegative4343 p) (nonnegative4340 p)
def d4345 (p : Pattern) : Int := if p 141 then d4344 p else d4338 p
theorem agree4345 (p q : Pattern) (h : Agree support p q) : d4345 p = d4345 q := by
  simp only [d4345, h 141 (by decide), agree4344 p q h, agree4338 p q h]
theorem nonnegative4345 (p : Pattern) : 0 ≤ d4345 p :=
  nonnegative_ite (p 141) (nonnegative4344 p) (nonnegative4338 p)
def d4346 (p : Pattern) : Int := if p 160 then d1062 p else d4334 p
theorem agree4346 (p q : Pattern) (h : Agree support p q) : d4346 p = d4346 q := by
  simp only [d4346, h 160 (by decide), agree1062 p q h, agree4334 p q h]
theorem nonnegative4346 (p : Pattern) : 0 ≤ d4346 p :=
  nonnegative_ite (p 160) (nonnegative1062 p) (nonnegative4334 p)
def d4347 (p : Pattern) : Int := if p 160 then d1062 p else d4340 p
theorem agree4347 (p q : Pattern) (h : Agree support p q) : d4347 p = d4347 q := by
  simp only [d4347, h 160 (by decide), agree1062 p q h, agree4340 p q h]
theorem nonnegative4347 (p : Pattern) : 0 ≤ d4347 p :=
  nonnegative_ite (p 160) (nonnegative1062 p) (nonnegative4340 p)
def d4348 (p : Pattern) : Int := if p 141 then d4347 p else d4346 p
theorem agree4348 (p q : Pattern) (h : Agree support p q) : d4348 p = d4348 q := by
  simp only [d4348, h 141 (by decide), agree4347 p q h, agree4346 p q h]
theorem nonnegative4348 (p : Pattern) : 0 ≤ d4348 p :=
  nonnegative_ite (p 141) (nonnegative4347 p) (nonnegative4346 p)
def d4349 (p : Pattern) : Int := if p 138 then d4348 p else d4345 p
theorem agree4349 (p q : Pattern) (h : Agree support p q) : d4349 p = d4349 q := by
  simp only [d4349, h 138 (by decide), agree4348 p q h, agree4345 p q h]
theorem nonnegative4349 (p : Pattern) : 0 ≤ d4349 p :=
  nonnegative_ite (p 138) (nonnegative4348 p) (nonnegative4345 p)
def d4350 (p : Pattern) : Int := if p 162 then d12 p else d60 p
theorem agree4350 (p q : Pattern) (h : Agree support p q) : d4350 p = d4350 q := by
  simp only [d4350, h 162 (by decide), agree12 p q h, agree60 p q h]
theorem nonnegative4350 (p : Pattern) : 0 ≤ d4350 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative60 p)
def d4351 (p : Pattern) : Int := if p 161 then d12 p else d4350 p
theorem agree4351 (p q : Pattern) (h : Agree support p q) : d4351 p = d4351 q := by
  simp only [d4351, h 161 (by decide), agree12 p q h, agree4350 p q h]
theorem nonnegative4351 (p : Pattern) : 0 ≤ d4351 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4350 p)
def d4352 (p : Pattern) : Int := if p 160 then d12 p else d4351 p
theorem agree4352 (p q : Pattern) (h : Agree support p q) : d4352 p = d4352 q := by
  simp only [d4352, h 160 (by decide), agree12 p q h, agree4351 p q h]
theorem nonnegative4352 (p : Pattern) : 0 ≤ d4352 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4351 p)
def d4353 (p : Pattern) : Int := if p 141 then d12 p else d4352 p
theorem agree4353 (p q : Pattern) (h : Agree support p q) : d4353 p = d4353 q := by
  simp only [d4353, h 141 (by decide), agree12 p q h, agree4352 p q h]
theorem nonnegative4353 (p : Pattern) : 0 ≤ d4353 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative4352 p)
def d4354 (p : Pattern) : Int := if p 138 then d4353 p else d4348 p
theorem agree4354 (p q : Pattern) (h : Agree support p q) : d4354 p = d4354 q := by
  simp only [d4354, h 138 (by decide), agree4353 p q h, agree4348 p q h]
theorem nonnegative4354 (p : Pattern) : 0 ≤ d4354 p :=
  nonnegative_ite (p 138) (nonnegative4353 p) (nonnegative4348 p)
def d4355 (p : Pattern) : Int := if p 116 then d4354 p else d4349 p
theorem agree4355 (p q : Pattern) (h : Agree support p q) : d4355 p = d4355 q := by
  simp only [d4355, h 116 (by decide), agree4354 p q h, agree4349 p q h]
theorem nonnegative4355 (p : Pattern) : 0 ≤ d4355 p :=
  nonnegative_ite (p 116) (nonnegative4354 p) (nonnegative4349 p)
def d4356 (p : Pattern) : Int := if p 138 then d12 p else d4348 p
theorem agree4356 (p q : Pattern) (h : Agree support p q) : d4356 p = d4356 q := by
  simp only [d4356, h 138 (by decide), agree12 p q h, agree4348 p q h]
theorem nonnegative4356 (p : Pattern) : 0 ≤ d4356 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4348 p)
def d4357 (p : Pattern) : Int := if p 116 then d4356 p else d4349 p
theorem agree4357 (p q : Pattern) (h : Agree support p q) : d4357 p = d4357 q := by
  simp only [d4357, h 116 (by decide), agree4356 p q h, agree4349 p q h]
theorem nonnegative4357 (p : Pattern) : 0 ≤ d4357 p :=
  nonnegative_ite (p 116) (nonnegative4356 p) (nonnegative4349 p)
def d4358 (p : Pattern) : Int := if p 115 then d4357 p else d4355 p
theorem agree4358 (p q : Pattern) (h : Agree support p q) : d4358 p = d4358 q := by
  simp only [d4358, h 115 (by decide), agree4357 p q h, agree4355 p q h]
theorem nonnegative4358 (p : Pattern) : 0 ≤ d4358 p :=
  nonnegative_ite (p 115) (nonnegative4357 p) (nonnegative4355 p)
def d4359 (p : Pattern) : Int := if p 71 then d4358 p else d4332 p
theorem agree4359 (p q : Pattern) (h : Agree support p q) : d4359 p = d4359 q := by
  simp only [d4359, h 71 (by decide), agree4358 p q h, agree4332 p q h]
theorem nonnegative4359 (p : Pattern) : 0 ≤ d4359 p :=
  nonnegative_ite (p 71) (nonnegative4358 p) (nonnegative4332 p)
def d4360 (p : Pattern) : Int := if p 49 then d4359 p else d4332 p
theorem agree4360 (p q : Pattern) (h : Agree support p q) : d4360 p = d4360 q := by
  simp only [d4360, h 49 (by decide), agree4359 p q h, agree4332 p q h]
theorem nonnegative4360 (p : Pattern) : 0 ≤ d4360 p :=
  nonnegative_ite (p 49) (nonnegative4359 p) (nonnegative4332 p)
def d4361 (p : Pattern) : Int := if p 161 then d4312 p else d53 p
theorem agree4361 (p q : Pattern) (h : Agree support p q) : d4361 p = d4361 q := by
  simp only [d4361, h 161 (by decide), agree4312 p q h, agree53 p q h]
theorem nonnegative4361 (p : Pattern) : 0 ≤ d4361 p :=
  nonnegative_ite (p 161) (nonnegative4312 p) (nonnegative53 p)
def d4362 (p : Pattern) : Int := if p 160 then d1101 p else d4361 p
theorem agree4362 (p q : Pattern) (h : Agree support p q) : d4362 p = d4362 q := by
  simp only [d4362, h 160 (by decide), agree1101 p q h, agree4361 p q h]
theorem nonnegative4362 (p : Pattern) : 0 ≤ d4362 p :=
  nonnegative_ite (p 160) (nonnegative1101 p) (nonnegative4361 p)
def d4363 (p : Pattern) : Int := if p 141 then d4362 p else d4320 p
theorem agree4363 (p q : Pattern) (h : Agree support p q) : d4363 p = d4363 q := by
  simp only [d4363, h 141 (by decide), agree4362 p q h, agree4320 p q h]
theorem nonnegative4363 (p : Pattern) : 0 ≤ d4363 p :=
  nonnegative_ite (p 141) (nonnegative4362 p) (nonnegative4320 p)
def d4364 (p : Pattern) : Int := if p 138 then d4363 p else d4318 p
theorem agree4364 (p q : Pattern) (h : Agree support p q) : d4364 p = d4364 q := by
  simp only [d4364, h 138 (by decide), agree4363 p q h, agree4318 p q h]
theorem nonnegative4364 (p : Pattern) : 0 ≤ d4364 p :=
  nonnegative_ite (p 138) (nonnegative4363 p) (nonnegative4318 p)
def d4365 (p : Pattern) : Int := if p 138 then d12 p else d4363 p
theorem agree4365 (p q : Pattern) (h : Agree support p q) : d4365 p = d4365 q := by
  simp only [d4365, h 138 (by decide), agree12 p q h, agree4363 p q h]
theorem nonnegative4365 (p : Pattern) : 0 ≤ d4365 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4363 p)
def d4366 (p : Pattern) : Int := if p 116 then d4365 p else d4364 p
theorem agree4366 (p q : Pattern) (h : Agree support p q) : d4366 p = d4366 q := by
  simp only [d4366, h 116 (by decide), agree4365 p q h, agree4364 p q h]
theorem nonnegative4366 (p : Pattern) : 0 ≤ d4366 p :=
  nonnegative_ite (p 116) (nonnegative4365 p) (nonnegative4364 p)
def d4367 (p : Pattern) : Int := if p 115 then d4366 p else d4329 p
theorem agree4367 (p q : Pattern) (h : Agree support p q) : d4367 p = d4367 q := by
  simp only [d4367, h 115 (by decide), agree4366 p q h, agree4329 p q h]
theorem nonnegative4367 (p : Pattern) : 0 ≤ d4367 p :=
  nonnegative_ite (p 115) (nonnegative4366 p) (nonnegative4329 p)
def d4368 (p : Pattern) : Int := if p 71 then d4367 p else d4332 p
theorem agree4368 (p q : Pattern) (h : Agree support p q) : d4368 p = d4368 q := by
  simp only [d4368, h 71 (by decide), agree4367 p q h, agree4332 p q h]
theorem nonnegative4368 (p : Pattern) : 0 ≤ d4368 p :=
  nonnegative_ite (p 71) (nonnegative4367 p) (nonnegative4332 p)
def d4369 (p : Pattern) : Int := if p 162 then d272 p else d269 p
theorem agree4369 (p q : Pattern) (h : Agree support p q) : d4369 p = d4369 q := by
  simp only [d4369, h 162 (by decide), agree272 p q h, agree269 p q h]
theorem nonnegative4369 (p : Pattern) : 0 ≤ d4369 p :=
  nonnegative_ite (p 162) (nonnegative272 p) (nonnegative269 p)
def d4370 (p : Pattern) : Int := if p 162 then d277 p else d272 p
theorem agree4370 (p q : Pattern) (h : Agree support p q) : d4370 p = d4370 q := by
  simp only [d4370, h 162 (by decide), agree277 p q h, agree272 p q h]
theorem nonnegative4370 (p : Pattern) : 0 ≤ d4370 p :=
  nonnegative_ite (p 162) (nonnegative277 p) (nonnegative272 p)
def d4371 (p : Pattern) : Int := if p 161 then d4370 p else d4369 p
theorem agree4371 (p q : Pattern) (h : Agree support p q) : d4371 p = d4371 q := by
  simp only [d4371, h 161 (by decide), agree4370 p q h, agree4369 p q h]
theorem nonnegative4371 (p : Pattern) : 0 ≤ d4371 p :=
  nonnegative_ite (p 161) (nonnegative4370 p) (nonnegative4369 p)
def d4372 (p : Pattern) : Int := if p 160 then d4371 p else d4334 p
theorem agree4372 (p q : Pattern) (h : Agree support p q) : d4372 p = d4372 q := by
  simp only [d4372, h 160 (by decide), agree4371 p q h, agree4334 p q h]
theorem nonnegative4372 (p : Pattern) : 0 ≤ d4372 p :=
  nonnegative_ite (p 160) (nonnegative4371 p) (nonnegative4334 p)
def d4373 (p : Pattern) : Int := if p 162 then d283 p else d132 p
theorem agree4373 (p q : Pattern) (h : Agree support p q) : d4373 p = d4373 q := by
  simp only [d4373, h 162 (by decide), agree283 p q h, agree132 p q h]
theorem nonnegative4373 (p : Pattern) : 0 ≤ d4373 p :=
  nonnegative_ite (p 162) (nonnegative283 p) (nonnegative132 p)
def d4374 (p : Pattern) : Int := if p 162 then d12 p else d283 p
theorem agree4374 (p q : Pattern) (h : Agree support p q) : d4374 p = d4374 q := by
  simp only [d4374, h 162 (by decide), agree12 p q h, agree283 p q h]
theorem nonnegative4374 (p : Pattern) : 0 ≤ d4374 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative283 p)
def d4375 (p : Pattern) : Int := if p 161 then d4374 p else d4373 p
theorem agree4375 (p q : Pattern) (h : Agree support p q) : d4375 p = d4375 q := by
  simp only [d4375, h 161 (by decide), agree4374 p q h, agree4373 p q h]
theorem nonnegative4375 (p : Pattern) : 0 ≤ d4375 p :=
  nonnegative_ite (p 161) (nonnegative4374 p) (nonnegative4373 p)
def d4376 (p : Pattern) : Int := if p 160 then d4375 p else d4340 p
theorem agree4376 (p q : Pattern) (h : Agree support p q) : d4376 p = d4376 q := by
  simp only [d4376, h 160 (by decide), agree4375 p q h, agree4340 p q h]
theorem nonnegative4376 (p : Pattern) : 0 ≤ d4376 p :=
  nonnegative_ite (p 160) (nonnegative4375 p) (nonnegative4340 p)
def d4377 (p : Pattern) : Int := if p 141 then d4376 p else d4372 p
theorem agree4377 (p q : Pattern) (h : Agree support p q) : d4377 p = d4377 q := by
  simp only [d4377, h 141 (by decide), agree4376 p q h, agree4372 p q h]
theorem nonnegative4377 (p : Pattern) : 0 ≤ d4377 p :=
  nonnegative_ite (p 141) (nonnegative4376 p) (nonnegative4372 p)
def d4378 (p : Pattern) : Int := if p 162 then d269 p else d105 p
theorem agree4378 (p q : Pattern) (h : Agree support p q) : d4378 p = d4378 q := by
  simp only [d4378, h 162 (by decide), agree269 p q h, agree105 p q h]
theorem nonnegative4378 (p : Pattern) : 0 ≤ d4378 p :=
  nonnegative_ite (p 162) (nonnegative269 p) (nonnegative105 p)
def d4379 (p : Pattern) : Int := if p 162 then d277 p else d269 p
theorem agree4379 (p q : Pattern) (h : Agree support p q) : d4379 p = d4379 q := by
  simp only [d4379, h 162 (by decide), agree277 p q h, agree269 p q h]
theorem nonnegative4379 (p : Pattern) : 0 ≤ d4379 p :=
  nonnegative_ite (p 162) (nonnegative277 p) (nonnegative269 p)
def d4380 (p : Pattern) : Int := if p 161 then d4379 p else d4378 p
theorem agree4380 (p q : Pattern) (h : Agree support p q) : d4380 p = d4380 q := by
  simp only [d4380, h 161 (by decide), agree4379 p q h, agree4378 p q h]
theorem nonnegative4380 (p : Pattern) : 0 ≤ d4380 p :=
  nonnegative_ite (p 161) (nonnegative4379 p) (nonnegative4378 p)
def d4381 (p : Pattern) : Int := if p 160 then d1062 p else d4380 p
theorem agree4381 (p q : Pattern) (h : Agree support p q) : d4381 p = d4381 q := by
  simp only [d4381, h 160 (by decide), agree1062 p q h, agree4380 p q h]
theorem nonnegative4381 (p : Pattern) : 0 ≤ d4381 p :=
  nonnegative_ite (p 160) (nonnegative1062 p) (nonnegative4380 p)
def d4382 (p : Pattern) : Int := if p 162 then d298 p else d132 p
theorem agree4382 (p q : Pattern) (h : Agree support p q) : d4382 p = d4382 q := by
  simp only [d4382, h 162 (by decide), agree298 p q h, agree132 p q h]
theorem nonnegative4382 (p : Pattern) : 0 ≤ d4382 p :=
  nonnegative_ite (p 162) (nonnegative298 p) (nonnegative132 p)
def d4383 (p : Pattern) : Int := if p 162 then d12 p else d298 p
theorem agree4383 (p q : Pattern) (h : Agree support p q) : d4383 p = d4383 q := by
  simp only [d4383, h 162 (by decide), agree12 p q h, agree298 p q h]
theorem nonnegative4383 (p : Pattern) : 0 ≤ d4383 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative298 p)
def d4384 (p : Pattern) : Int := if p 161 then d4383 p else d4382 p
theorem agree4384 (p q : Pattern) (h : Agree support p q) : d4384 p = d4384 q := by
  simp only [d4384, h 161 (by decide), agree4383 p q h, agree4382 p q h]
theorem nonnegative4384 (p : Pattern) : 0 ≤ d4384 p :=
  nonnegative_ite (p 161) (nonnegative4383 p) (nonnegative4382 p)
def d4385 (p : Pattern) : Int := if p 160 then d1141 p else d4384 p
theorem agree4385 (p q : Pattern) (h : Agree support p q) : d4385 p = d4385 q := by
  simp only [d4385, h 160 (by decide), agree1141 p q h, agree4384 p q h]
theorem nonnegative4385 (p : Pattern) : 0 ≤ d4385 p :=
  nonnegative_ite (p 160) (nonnegative1141 p) (nonnegative4384 p)
def d4386 (p : Pattern) : Int := if p 141 then d4385 p else d4381 p
theorem agree4386 (p q : Pattern) (h : Agree support p q) : d4386 p = d4386 q := by
  simp only [d4386, h 141 (by decide), agree4385 p q h, agree4381 p q h]
theorem nonnegative4386 (p : Pattern) : 0 ≤ d4386 p :=
  nonnegative_ite (p 141) (nonnegative4385 p) (nonnegative4381 p)
def d4387 (p : Pattern) : Int := if p 138 then d4386 p else d4377 p
theorem agree4387 (p q : Pattern) (h : Agree support p q) : d4387 p = d4387 q := by
  simp only [d4387, h 138 (by decide), agree4386 p q h, agree4377 p q h]
theorem nonnegative4387 (p : Pattern) : 0 ≤ d4387 p :=
  nonnegative_ite (p 138) (nonnegative4386 p) (nonnegative4377 p)
def d4388 (p : Pattern) : Int := if p 138 then d12 p else d4386 p
theorem agree4388 (p q : Pattern) (h : Agree support p q) : d4388 p = d4388 q := by
  simp only [d4388, h 138 (by decide), agree12 p q h, agree4386 p q h]
theorem nonnegative4388 (p : Pattern) : 0 ≤ d4388 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4386 p)
def d4389 (p : Pattern) : Int := if p 116 then d4388 p else d4387 p
theorem agree4389 (p q : Pattern) (h : Agree support p q) : d4389 p = d4389 q := by
  simp only [d4389, h 116 (by decide), agree4388 p q h, agree4387 p q h]
theorem nonnegative4389 (p : Pattern) : 0 ≤ d4389 p :=
  nonnegative_ite (p 116) (nonnegative4388 p) (nonnegative4387 p)
def d4390 (p : Pattern) : Int := if p 115 then d4389 p else d4355 p
theorem agree4390 (p q : Pattern) (h : Agree support p q) : d4390 p = d4390 q := by
  simp only [d4390, h 115 (by decide), agree4389 p q h, agree4355 p q h]
theorem nonnegative4390 (p : Pattern) : 0 ≤ d4390 p :=
  nonnegative_ite (p 115) (nonnegative4389 p) (nonnegative4355 p)
def d4391 (p : Pattern) : Int := if p 71 then d4390 p else d4332 p
theorem agree4391 (p q : Pattern) (h : Agree support p q) : d4391 p = d4391 q := by
  simp only [d4391, h 71 (by decide), agree4390 p q h, agree4332 p q h]
theorem nonnegative4391 (p : Pattern) : 0 ≤ d4391 p :=
  nonnegative_ite (p 71) (nonnegative4390 p) (nonnegative4332 p)
def d4392 (p : Pattern) : Int := if p 49 then d4391 p else d4368 p
theorem agree4392 (p q : Pattern) (h : Agree support p q) : d4392 p = d4392 q := by
  simp only [d4392, h 49 (by decide), agree4391 p q h, agree4368 p q h]
theorem nonnegative4392 (p : Pattern) : 0 ≤ d4392 p :=
  nonnegative_ite (p 49) (nonnegative4391 p) (nonnegative4368 p)
def d4393 (p : Pattern) : Int := if p 48 then d4392 p else d4360 p
theorem agree4393 (p q : Pattern) (h : Agree support p q) : d4393 p = d4393 q := by
  simp only [d4393, h 48 (by decide), agree4392 p q h, agree4360 p q h]
theorem nonnegative4393 (p : Pattern) : 0 ≤ d4393 p :=
  nonnegative_ite (p 48) (nonnegative4392 p) (nonnegative4360 p)
def d4394 (p : Pattern) : Int := if p 162 then d1 p else d0 p
theorem agree4394 (p q : Pattern) (h : Agree support p q) : d4394 p = d4394 q := by
  simp only [d4394, h 162 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4394 (p : Pattern) : 0 ≤ d4394 p :=
  nonnegative_ite (p 162) (nonnegative1 p) (nonnegative0 p)
def d4395 (p : Pattern) : Int := if p 162 then d0 p else d1 p
theorem agree4395 (p q : Pattern) (h : Agree support p q) : d4395 p = d4395 q := by
  simp only [d4395, h 162 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4395 (p : Pattern) : 0 ≤ d4395 p :=
  nonnegative_ite (p 162) (nonnegative0 p) (nonnegative1 p)
def d4396 (p : Pattern) : Int := if p 141 then d0 p else d4395 p
theorem agree4396 (p q : Pattern) (h : Agree support p q) : d4396 p = d4396 q := by
  simp only [d4396, h 141 (by decide), agree0 p q h, agree4395 p q h]
theorem nonnegative4396 (p : Pattern) : 0 ≤ d4396 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative4395 p)
def d4397 (p : Pattern) : Int := if p 162 then d0 p else d4148 p
theorem agree4397 (p q : Pattern) (h : Agree support p q) : d4397 p = d4397 q := by
  simp only [d4397, h 162 (by decide), agree0 p q h, agree4148 p q h]
theorem nonnegative4397 (p : Pattern) : 0 ≤ d4397 p :=
  nonnegative_ite (p 162) (nonnegative0 p) (nonnegative4148 p)
def d4398 (p : Pattern) : Int := if p 141 then d0 p else d4397 p
theorem agree4398 (p q : Pattern) (h : Agree support p q) : d4398 p = d4398 q := by
  simp only [d4398, h 141 (by decide), agree0 p q h, agree4397 p q h]
theorem nonnegative4398 (p : Pattern) : 0 ≤ d4398 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative4397 p)
def d4399 (p : Pattern) : Int := if p 141 then d85 p else d81 p
theorem agree4399 (p q : Pattern) (h : Agree support p q) : d4399 p = d4399 q := by
  simp only [d4399, h 141 (by decide), agree85 p q h, agree81 p q h]
theorem nonnegative4399 (p : Pattern) : 0 ≤ d4399 p :=
  nonnegative_ite (p 141) (nonnegative85 p) (nonnegative81 p)
def d4400 (p : Pattern) : Int := if p 138 then d4399 p else d4120 p
theorem agree4400 (p q : Pattern) (h : Agree support p q) : d4400 p = d4400 q := by
  simp only [d4400, h 138 (by decide), agree4399 p q h, agree4120 p q h]
theorem nonnegative4400 (p : Pattern) : 0 ≤ d4400 p :=
  nonnegative_ite (p 138) (nonnegative4399 p) (nonnegative4120 p)
def d4401 (p : Pattern) : Int := if p 141 then d12 p else d93 p
theorem agree4401 (p q : Pattern) (h : Agree support p q) : d4401 p = d4401 q := by
  simp only [d4401, h 141 (by decide), agree12 p q h, agree93 p q h]
theorem nonnegative4401 (p : Pattern) : 0 ≤ d4401 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative93 p)
def d4402 (p : Pattern) : Int := if p 138 then d4401 p else d4399 p
theorem agree4402 (p q : Pattern) (h : Agree support p q) : d4402 p = d4402 q := by
  simp only [d4402, h 138 (by decide), agree4401 p q h, agree4399 p q h]
theorem nonnegative4402 (p : Pattern) : 0 ≤ d4402 p :=
  nonnegative_ite (p 138) (nonnegative4401 p) (nonnegative4399 p)
def d4403 (p : Pattern) : Int := if p 116 then d4402 p else d4400 p
theorem agree4403 (p q : Pattern) (h : Agree support p q) : d4403 p = d4403 q := by
  simp only [d4403, h 116 (by decide), agree4402 p q h, agree4400 p q h]
theorem nonnegative4403 (p : Pattern) : 0 ≤ d4403 p :=
  nonnegative_ite (p 116) (nonnegative4402 p) (nonnegative4400 p)
def d4404 (p : Pattern) : Int := if p 138 then d12 p else d4399 p
theorem agree4404 (p q : Pattern) (h : Agree support p q) : d4404 p = d4404 q := by
  simp only [d4404, h 138 (by decide), agree12 p q h, agree4399 p q h]
theorem nonnegative4404 (p : Pattern) : 0 ≤ d4404 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4399 p)
def d4405 (p : Pattern) : Int := if p 116 then d4404 p else d4400 p
theorem agree4405 (p q : Pattern) (h : Agree support p q) : d4405 p = d4405 q := by
  simp only [d4405, h 116 (by decide), agree4404 p q h, agree4400 p q h]
theorem nonnegative4405 (p : Pattern) : 0 ≤ d4405 p :=
  nonnegative_ite (p 116) (nonnegative4404 p) (nonnegative4400 p)
def d4406 (p : Pattern) : Int := if p 115 then d4405 p else d4403 p
theorem agree4406 (p q : Pattern) (h : Agree support p q) : d4406 p = d4406 q := by
  simp only [d4406, h 115 (by decide), agree4405 p q h, agree4403 p q h]
theorem nonnegative4406 (p : Pattern) : 0 ≤ d4406 p :=
  nonnegative_ite (p 115) (nonnegative4405 p) (nonnegative4403 p)
def d4407 (p : Pattern) : Int := if p 141 then d155 p else d151 p
theorem agree4407 (p q : Pattern) (h : Agree support p q) : d4407 p = d4407 q := by
  simp only [d4407, h 141 (by decide), agree155 p q h, agree151 p q h]
theorem nonnegative4407 (p : Pattern) : 0 ≤ d4407 p :=
  nonnegative_ite (p 141) (nonnegative155 p) (nonnegative151 p)
def d4408 (p : Pattern) : Int := if p 138 then d4407 p else d4123 p
theorem agree4408 (p q : Pattern) (h : Agree support p q) : d4408 p = d4408 q := by
  simp only [d4408, h 138 (by decide), agree4407 p q h, agree4123 p q h]
theorem nonnegative4408 (p : Pattern) : 0 ≤ d4408 p :=
  nonnegative_ite (p 138) (nonnegative4407 p) (nonnegative4123 p)
def d4409 (p : Pattern) : Int := if p 138 then d12 p else d4407 p
theorem agree4409 (p q : Pattern) (h : Agree support p q) : d4409 p = d4409 q := by
  simp only [d4409, h 138 (by decide), agree12 p q h, agree4407 p q h]
theorem nonnegative4409 (p : Pattern) : 0 ≤ d4409 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4407 p)
def d4410 (p : Pattern) : Int := if p 116 then d4409 p else d4408 p
theorem agree4410 (p q : Pattern) (h : Agree support p q) : d4410 p = d4410 q := by
  simp only [d4410, h 116 (by decide), agree4409 p q h, agree4408 p q h]
theorem nonnegative4410 (p : Pattern) : 0 ≤ d4410 p :=
  nonnegative_ite (p 116) (nonnegative4409 p) (nonnegative4408 p)
def d4411 (p : Pattern) : Int := if p 71 then d4410 p else d4406 p
theorem agree4411 (p q : Pattern) (h : Agree support p q) : d4411 p = d4411 q := by
  simp only [d4411, h 71 (by decide), agree4410 p q h, agree4406 p q h]
theorem nonnegative4411 (p : Pattern) : 0 ≤ d4411 p :=
  nonnegative_ite (p 71) (nonnegative4410 p) (nonnegative4406 p)
def d4412 (p : Pattern) : Int := if p 49 then d4411 p else d4406 p
theorem agree4412 (p q : Pattern) (h : Agree support p q) : d4412 p = d4412 q := by
  simp only [d4412, h 49 (by decide), agree4411 p q h, agree4406 p q h]
theorem nonnegative4412 (p : Pattern) : 0 ≤ d4412 p :=
  nonnegative_ite (p 49) (nonnegative4411 p) (nonnegative4406 p)
def d4413 (p : Pattern) : Int := if p 141 then d185 p else d178 p
theorem agree4413 (p q : Pattern) (h : Agree support p q) : d4413 p = d4413 q := by
  simp only [d4413, h 141 (by decide), agree185 p q h, agree178 p q h]
theorem nonnegative4413 (p : Pattern) : 0 ≤ d4413 p :=
  nonnegative_ite (p 141) (nonnegative185 p) (nonnegative178 p)
def d4414 (p : Pattern) : Int := if p 141 then d203 p else d196 p
theorem agree4414 (p q : Pattern) (h : Agree support p q) : d4414 p = d4414 q := by
  simp only [d4414, h 141 (by decide), agree203 p q h, agree196 p q h]
theorem nonnegative4414 (p : Pattern) : 0 ≤ d4414 p :=
  nonnegative_ite (p 141) (nonnegative203 p) (nonnegative196 p)
def d4415 (p : Pattern) : Int := if p 138 then d4414 p else d4413 p
theorem agree4415 (p q : Pattern) (h : Agree support p q) : d4415 p = d4415 q := by
  simp only [d4415, h 138 (by decide), agree4414 p q h, agree4413 p q h]
theorem nonnegative4415 (p : Pattern) : 0 ≤ d4415 p :=
  nonnegative_ite (p 138) (nonnegative4414 p) (nonnegative4413 p)
def d4416 (p : Pattern) : Int := if p 138 then d12 p else d4414 p
theorem agree4416 (p q : Pattern) (h : Agree support p q) : d4416 p = d4416 q := by
  simp only [d4416, h 138 (by decide), agree12 p q h, agree4414 p q h]
theorem nonnegative4416 (p : Pattern) : 0 ≤ d4416 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4414 p)
def d4417 (p : Pattern) : Int := if p 116 then d4416 p else d4415 p
theorem agree4417 (p q : Pattern) (h : Agree support p q) : d4417 p = d4417 q := by
  simp only [d4417, h 116 (by decide), agree4416 p q h, agree4415 p q h]
theorem nonnegative4417 (p : Pattern) : 0 ≤ d4417 p :=
  nonnegative_ite (p 116) (nonnegative4416 p) (nonnegative4415 p)
def d4418 (p : Pattern) : Int := if p 115 then d4417 p else d4403 p
theorem agree4418 (p q : Pattern) (h : Agree support p q) : d4418 p = d4418 q := by
  simp only [d4418, h 115 (by decide), agree4417 p q h, agree4403 p q h]
theorem nonnegative4418 (p : Pattern) : 0 ≤ d4418 p :=
  nonnegative_ite (p 115) (nonnegative4417 p) (nonnegative4403 p)
def d4419 (p : Pattern) : Int := if p 71 then d4418 p else d4406 p
theorem agree4419 (p q : Pattern) (h : Agree support p q) : d4419 p = d4419 q := by
  simp only [d4419, h 71 (by decide), agree4418 p q h, agree4406 p q h]
theorem nonnegative4419 (p : Pattern) : 0 ≤ d4419 p :=
  nonnegative_ite (p 71) (nonnegative4418 p) (nonnegative4406 p)
def d4420 (p : Pattern) : Int := if p 138 then d4407 p else d4132 p
theorem agree4420 (p q : Pattern) (h : Agree support p q) : d4420 p = d4420 q := by
  simp only [d4420, h 138 (by decide), agree4407 p q h, agree4132 p q h]
theorem nonnegative4420 (p : Pattern) : 0 ≤ d4420 p :=
  nonnegative_ite (p 138) (nonnegative4407 p) (nonnegative4132 p)
def d4421 (p : Pattern) : Int := if p 116 then d4409 p else d4420 p
theorem agree4421 (p q : Pattern) (h : Agree support p q) : d4421 p = d4421 q := by
  simp only [d4421, h 116 (by decide), agree4409 p q h, agree4420 p q h]
theorem nonnegative4421 (p : Pattern) : 0 ≤ d4421 p :=
  nonnegative_ite (p 116) (nonnegative4409 p) (nonnegative4420 p)
def d4422 (p : Pattern) : Int := if p 141 then d238 p else d232 p
theorem agree4422 (p q : Pattern) (h : Agree support p q) : d4422 p = d4422 q := by
  simp only [d4422, h 141 (by decide), agree238 p q h, agree232 p q h]
theorem nonnegative4422 (p : Pattern) : 0 ≤ d4422 p :=
  nonnegative_ite (p 141) (nonnegative238 p) (nonnegative232 p)
def d4423 (p : Pattern) : Int := if p 141 then d248 p else d155 p
theorem agree4423 (p q : Pattern) (h : Agree support p q) : d4423 p = d4423 q := by
  simp only [d4423, h 141 (by decide), agree248 p q h, agree155 p q h]
theorem nonnegative4423 (p : Pattern) : 0 ≤ d4423 p :=
  nonnegative_ite (p 141) (nonnegative248 p) (nonnegative155 p)
def d4424 (p : Pattern) : Int := if p 138 then d4423 p else d4422 p
theorem agree4424 (p q : Pattern) (h : Agree support p q) : d4424 p = d4424 q := by
  simp only [d4424, h 138 (by decide), agree4423 p q h, agree4422 p q h]
theorem nonnegative4424 (p : Pattern) : 0 ≤ d4424 p :=
  nonnegative_ite (p 138) (nonnegative4423 p) (nonnegative4422 p)
def d4425 (p : Pattern) : Int := if p 141 then d248 p else d259 p
theorem agree4425 (p q : Pattern) (h : Agree support p q) : d4425 p = d4425 q := by
  simp only [d4425, h 141 (by decide), agree248 p q h, agree259 p q h]
theorem nonnegative4425 (p : Pattern) : 0 ≤ d4425 p :=
  nonnegative_ite (p 141) (nonnegative248 p) (nonnegative259 p)
def d4426 (p : Pattern) : Int := if p 138 then d12 p else d4425 p
theorem agree4426 (p q : Pattern) (h : Agree support p q) : d4426 p = d4426 q := by
  simp only [d4426, h 138 (by decide), agree12 p q h, agree4425 p q h]
theorem nonnegative4426 (p : Pattern) : 0 ≤ d4426 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4425 p)
def d4427 (p : Pattern) : Int := if p 116 then d4426 p else d4424 p
theorem agree4427 (p q : Pattern) (h : Agree support p q) : d4427 p = d4427 q := by
  simp only [d4427, h 116 (by decide), agree4426 p q h, agree4424 p q h]
theorem nonnegative4427 (p : Pattern) : 0 ≤ d4427 p :=
  nonnegative_ite (p 116) (nonnegative4426 p) (nonnegative4424 p)
def d4428 (p : Pattern) : Int := if p 115 then d4427 p else d4421 p
theorem agree4428 (p q : Pattern) (h : Agree support p q) : d4428 p = d4428 q := by
  simp only [d4428, h 115 (by decide), agree4427 p q h, agree4421 p q h]
theorem nonnegative4428 (p : Pattern) : 0 ≤ d4428 p :=
  nonnegative_ite (p 115) (nonnegative4427 p) (nonnegative4421 p)
def d4429 (p : Pattern) : Int := if p 71 then d4428 p else d4406 p
theorem agree4429 (p q : Pattern) (h : Agree support p q) : d4429 p = d4429 q := by
  simp only [d4429, h 71 (by decide), agree4428 p q h, agree4406 p q h]
theorem nonnegative4429 (p : Pattern) : 0 ≤ d4429 p :=
  nonnegative_ite (p 71) (nonnegative4428 p) (nonnegative4406 p)
def d4430 (p : Pattern) : Int := if p 49 then d4429 p else d4419 p
theorem agree4430 (p q : Pattern) (h : Agree support p q) : d4430 p = d4430 q := by
  simp only [d4430, h 49 (by decide), agree4429 p q h, agree4419 p q h]
theorem nonnegative4430 (p : Pattern) : 0 ≤ d4430 p :=
  nonnegative_ite (p 49) (nonnegative4429 p) (nonnegative4419 p)
def d4431 (p : Pattern) : Int := if p 48 then d4430 p else d4412 p
theorem agree4431 (p q : Pattern) (h : Agree support p q) : d4431 p = d4431 q := by
  simp only [d4431, h 48 (by decide), agree4430 p q h, agree4412 p q h]
theorem nonnegative4431 (p : Pattern) : 0 ≤ d4431 p :=
  nonnegative_ite (p 48) (nonnegative4430 p) (nonnegative4412 p)
def d4432 (p : Pattern) : Int := if p 160 then d4299 p else d0 p
theorem agree4432 (p q : Pattern) (h : Agree support p q) : d4432 p = d4432 q := by
  simp only [d4432, h 160 (by decide), agree4299 p q h, agree0 p q h]
theorem nonnegative4432 (p : Pattern) : 0 ≤ d4432 p :=
  nonnegative_ite (p 160) (nonnegative4299 p) (nonnegative0 p)
def d4433 (p : Pattern) : Int := if p 141 then d64 p else d28 p
theorem agree4433 (p q : Pattern) (h : Agree support p q) : d4433 p = d4433 q := by
  simp only [d4433, h 141 (by decide), agree64 p q h, agree28 p q h]
theorem nonnegative4433 (p : Pattern) : 0 ≤ d4433 p :=
  nonnegative_ite (p 141) (nonnegative64 p) (nonnegative28 p)
def d4434 (p : Pattern) : Int := if p 141 then d12 p else d91 p
theorem agree4434 (p q : Pattern) (h : Agree support p q) : d4434 p = d4434 q := by
  simp only [d4434, h 141 (by decide), agree12 p q h, agree91 p q h]
theorem nonnegative4434 (p : Pattern) : 0 ≤ d4434 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative91 p)
def d4435 (p : Pattern) : Int := if p 138 then d4434 p else d4433 p
theorem agree4435 (p q : Pattern) (h : Agree support p q) : d4435 p = d4435 q := by
  simp only [d4435, h 138 (by decide), agree4434 p q h, agree4433 p q h]
theorem nonnegative4435 (p : Pattern) : 0 ≤ d4435 p :=
  nonnegative_ite (p 138) (nonnegative4434 p) (nonnegative4433 p)
def d4436 (p : Pattern) : Int := if p 116 then d4435 p else d4433 p
theorem agree4436 (p q : Pattern) (h : Agree support p q) : d4436 p = d4436 q := by
  simp only [d4436, h 116 (by decide), agree4435 p q h, agree4433 p q h]
theorem nonnegative4436 (p : Pattern) : 0 ≤ d4436 p :=
  nonnegative_ite (p 116) (nonnegative4435 p) (nonnegative4433 p)
def d4437 (p : Pattern) : Int := if p 138 then d12 p else d4433 p
theorem agree4437 (p q : Pattern) (h : Agree support p q) : d4437 p = d4437 q := by
  simp only [d4437, h 138 (by decide), agree12 p q h, agree4433 p q h]
theorem nonnegative4437 (p : Pattern) : 0 ≤ d4437 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4433 p)
def d4438 (p : Pattern) : Int := if p 116 then d4437 p else d4433 p
theorem agree4438 (p q : Pattern) (h : Agree support p q) : d4438 p = d4438 q := by
  simp only [d4438, h 116 (by decide), agree4437 p q h, agree4433 p q h]
theorem nonnegative4438 (p : Pattern) : 0 ≤ d4438 p :=
  nonnegative_ite (p 116) (nonnegative4437 p) (nonnegative4433 p)
def d4439 (p : Pattern) : Int := if p 115 then d4438 p else d4436 p
theorem agree4439 (p q : Pattern) (h : Agree support p q) : d4439 p = d4439 q := by
  simp only [d4439, h 115 (by decide), agree4438 p q h, agree4436 p q h]
theorem nonnegative4439 (p : Pattern) : 0 ≤ d4439 p :=
  nonnegative_ite (p 115) (nonnegative4438 p) (nonnegative4436 p)
end NetHack.Sokoban22Refined85
