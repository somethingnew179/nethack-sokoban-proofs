/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes52
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6360 (p : Pattern) : Int := if p 182 then d6359 p else d10 p
theorem agree6360 (p q : Pattern) (h : Agree support p q) : d6360 p = d6360 q := by
  simp only [d6360, h 182 (by decide), agree6359 p q h, agree10 p q h]
theorem nonnegative6360 (p : Pattern) : 0 ≤ d6360 p :=
  nonnegative_ite (p 182) (nonnegative6359 p) (nonnegative10 p)
def d6361 (p : Pattern) : Int := if p 163 then d6360 p else d6330 p
theorem agree6361 (p q : Pattern) (h : Agree support p q) : d6361 p = d6361 q := by
  simp only [d6361, h 163 (by decide), agree6360 p q h, agree6330 p q h]
theorem nonnegative6361 (p : Pattern) : 0 ≤ d6361 p :=
  nonnegative_ite (p 163) (nonnegative6360 p) (nonnegative6330 p)
def d6362 (p : Pattern) : Int := if p 182 then d6343 p else d11 p
theorem agree6362 (p q : Pattern) (h : Agree support p q) : d6362 p = d6362 q := by
  simp only [d6362, h 182 (by decide), agree6343 p q h, agree11 p q h]
theorem nonnegative6362 (p : Pattern) : 0 ≤ d6362 p :=
  nonnegative_ite (p 182) (nonnegative6343 p) (nonnegative11 p)
def d6363 (p : Pattern) : Int := if p 163 then d12 p else d6362 p
theorem agree6363 (p q : Pattern) (h : Agree support p q) : d6363 p = d6363 q := by
  simp only [d6363, h 163 (by decide), agree12 p q h, agree6362 p q h]
theorem nonnegative6363 (p : Pattern) : 0 ≤ d6363 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6362 p)
def d6364 (p : Pattern) : Int := if p 162 then d6363 p else d6361 p
theorem agree6364 (p q : Pattern) (h : Agree support p q) : d6364 p = d6364 q := by
  simp only [d6364, h 162 (by decide), agree6363 p q h, agree6361 p q h]
theorem nonnegative6364 (p : Pattern) : 0 ≤ d6364 p :=
  nonnegative_ite (p 162) (nonnegative6363 p) (nonnegative6361 p)
def d6365 (p : Pattern) : Int := if p 161 then d6364 p else d6358 p
theorem agree6365 (p q : Pattern) (h : Agree support p q) : d6365 p = d6365 q := by
  simp only [d6365, h 161 (by decide), agree6364 p q h, agree6358 p q h]
theorem nonnegative6365 (p : Pattern) : 0 ≤ d6365 p :=
  nonnegative_ite (p 161) (nonnegative6364 p) (nonnegative6358 p)
def d6366 (p : Pattern) : Int := if p 182 then d12 p else d2 p
theorem agree6366 (p q : Pattern) (h : Agree support p q) : d6366 p = d6366 q := by
  simp only [d6366, h 182 (by decide), agree12 p q h, agree2 p q h]
theorem nonnegative6366 (p : Pattern) : 0 ≤ d6366 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2 p)
def d6367 (p : Pattern) : Int := if p 163 then d6366 p else d6341 p
theorem agree6367 (p q : Pattern) (h : Agree support p q) : d6367 p = d6367 q := by
  simp only [d6367, h 163 (by decide), agree6366 p q h, agree6341 p q h]
theorem nonnegative6367 (p : Pattern) : 0 ≤ d6367 p :=
  nonnegative_ite (p 163) (nonnegative6366 p) (nonnegative6341 p)
def d6368 (p : Pattern) : Int := if p 163 then d6350 p else d6345 p
theorem agree6368 (p q : Pattern) (h : Agree support p q) : d6368 p = d6368 q := by
  simp only [d6368, h 163 (by decide), agree6350 p q h, agree6345 p q h]
theorem nonnegative6368 (p : Pattern) : 0 ≤ d6368 p :=
  nonnegative_ite (p 163) (nonnegative6350 p) (nonnegative6345 p)
def d6369 (p : Pattern) : Int := if p 162 then d6368 p else d6367 p
theorem agree6369 (p q : Pattern) (h : Agree support p q) : d6369 p = d6369 q := by
  simp only [d6369, h 162 (by decide), agree6368 p q h, agree6367 p q h]
theorem nonnegative6369 (p : Pattern) : 0 ≤ d6369 p :=
  nonnegative_ite (p 162) (nonnegative6368 p) (nonnegative6367 p)
def d6370 (p : Pattern) : Int := if p 182 then d12 p else d10 p
theorem agree6370 (p q : Pattern) (h : Agree support p q) : d6370 p = d6370 q := by
  simp only [d6370, h 182 (by decide), agree12 p q h, agree10 p q h]
theorem nonnegative6370 (p : Pattern) : 0 ≤ d6370 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative10 p)
def d6371 (p : Pattern) : Int := if p 163 then d6370 p else d6345 p
theorem agree6371 (p q : Pattern) (h : Agree support p q) : d6371 p = d6371 q := by
  simp only [d6371, h 163 (by decide), agree6370 p q h, agree6345 p q h]
theorem nonnegative6371 (p : Pattern) : 0 ≤ d6371 p :=
  nonnegative_ite (p 163) (nonnegative6370 p) (nonnegative6345 p)
def d6372 (p : Pattern) : Int := if p 182 then d12 p else d11 p
theorem agree6372 (p q : Pattern) (h : Agree support p q) : d6372 p = d6372 q := by
  simp only [d6372, h 182 (by decide), agree12 p q h, agree11 p q h]
theorem nonnegative6372 (p : Pattern) : 0 ≤ d6372 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative11 p)
def d6373 (p : Pattern) : Int := if p 163 then d12 p else d6372 p
theorem agree6373 (p q : Pattern) (h : Agree support p q) : d6373 p = d6373 q := by
  simp only [d6373, h 163 (by decide), agree12 p q h, agree6372 p q h]
theorem nonnegative6373 (p : Pattern) : 0 ≤ d6373 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6372 p)
def d6374 (p : Pattern) : Int := if p 162 then d6373 p else d6371 p
theorem agree6374 (p q : Pattern) (h : Agree support p q) : d6374 p = d6374 q := by
  simp only [d6374, h 162 (by decide), agree6373 p q h, agree6371 p q h]
theorem nonnegative6374 (p : Pattern) : 0 ≤ d6374 p :=
  nonnegative_ite (p 162) (nonnegative6373 p) (nonnegative6371 p)
def d6375 (p : Pattern) : Int := if p 161 then d6374 p else d6369 p
theorem agree6375 (p q : Pattern) (h : Agree support p q) : d6375 p = d6375 q := by
  simp only [d6375, h 161 (by decide), agree6374 p q h, agree6369 p q h]
theorem nonnegative6375 (p : Pattern) : 0 ≤ d6375 p :=
  nonnegative_ite (p 161) (nonnegative6374 p) (nonnegative6369 p)
def d6376 (p : Pattern) : Int := if p 160 then d6375 p else d6365 p
theorem agree6376 (p q : Pattern) (h : Agree support p q) : d6376 p = d6376 q := by
  simp only [d6376, h 160 (by decide), agree6375 p q h, agree6365 p q h]
theorem nonnegative6376 (p : Pattern) : 0 ≤ d6376 p :=
  nonnegative_ite (p 160) (nonnegative6375 p) (nonnegative6365 p)
def d6377 (p : Pattern) : Int := if p 141 then d6376 p else d6354 p
theorem agree6377 (p q : Pattern) (h : Agree support p q) : d6377 p = d6377 q := by
  simp only [d6377, h 141 (by decide), agree6376 p q h, agree6354 p q h]
theorem nonnegative6377 (p : Pattern) : 0 ≤ d6377 p :=
  nonnegative_ite (p 141) (nonnegative6376 p) (nonnegative6354 p)
def d6378 (p : Pattern) : Int := if p 182 then d6340 p else d6 p
theorem agree6378 (p q : Pattern) (h : Agree support p q) : d6378 p = d6378 q := by
  simp only [d6378, h 182 (by decide), agree6340 p q h, agree6 p q h]
theorem nonnegative6378 (p : Pattern) : 0 ≤ d6378 p :=
  nonnegative_ite (p 182) (nonnegative6340 p) (nonnegative6 p)
def d6379 (p : Pattern) : Int := if p 163 then d6378 p else d6355 p
theorem agree6379 (p q : Pattern) (h : Agree support p q) : d6379 p = d6379 q := by
  simp only [d6379, h 163 (by decide), agree6378 p q h, agree6355 p q h]
theorem nonnegative6379 (p : Pattern) : 0 ≤ d6379 p :=
  nonnegative_ite (p 163) (nonnegative6378 p) (nonnegative6355 p)
def d6380 (p : Pattern) : Int := if p 162 then d6363 p else d6379 p
theorem agree6380 (p q : Pattern) (h : Agree support p q) : d6380 p = d6380 q := by
  simp only [d6380, h 162 (by decide), agree6363 p q h, agree6379 p q h]
theorem nonnegative6380 (p : Pattern) : 0 ≤ d6380 p :=
  nonnegative_ite (p 162) (nonnegative6363 p) (nonnegative6379 p)
def d6381 (p : Pattern) : Int := if p 161 then d12 p else d6380 p
theorem agree6381 (p q : Pattern) (h : Agree support p q) : d6381 p = d6381 q := by
  simp only [d6381, h 161 (by decide), agree12 p q h, agree6380 p q h]
theorem nonnegative6381 (p : Pattern) : 0 ≤ d6381 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6380 p)
def d6382 (p : Pattern) : Int := if p 160 then d6381 p else d6337 p
theorem agree6382 (p q : Pattern) (h : Agree support p q) : d6382 p = d6382 q := by
  simp only [d6382, h 160 (by decide), agree6381 p q h, agree6337 p q h]
theorem nonnegative6382 (p : Pattern) : 0 ≤ d6382 p :=
  nonnegative_ite (p 160) (nonnegative6381 p) (nonnegative6337 p)
def d6383 (p : Pattern) : Int := if p 163 then d12 p else d6378 p
theorem agree6383 (p q : Pattern) (h : Agree support p q) : d6383 p = d6383 q := by
  simp only [d6383, h 163 (by decide), agree12 p q h, agree6378 p q h]
theorem nonnegative6383 (p : Pattern) : 0 ≤ d6383 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6378 p)
def d6384 (p : Pattern) : Int := if p 162 then d12 p else d6383 p
theorem agree6384 (p q : Pattern) (h : Agree support p q) : d6384 p = d6384 q := by
  simp only [d6384, h 162 (by decide), agree12 p q h, agree6383 p q h]
theorem nonnegative6384 (p : Pattern) : 0 ≤ d6384 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6383 p)
def d6385 (p : Pattern) : Int := if p 161 then d12 p else d6384 p
theorem agree6385 (p q : Pattern) (h : Agree support p q) : d6385 p = d6385 q := by
  simp only [d6385, h 161 (by decide), agree12 p q h, agree6384 p q h]
theorem nonnegative6385 (p : Pattern) : 0 ≤ d6385 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6384 p)
def d6386 (p : Pattern) : Int := if p 160 then d6385 p else d6365 p
theorem agree6386 (p q : Pattern) (h : Agree support p q) : d6386 p = d6386 q := by
  simp only [d6386, h 160 (by decide), agree6385 p q h, agree6365 p q h]
theorem nonnegative6386 (p : Pattern) : 0 ≤ d6386 p :=
  nonnegative_ite (p 160) (nonnegative6385 p) (nonnegative6365 p)
def d6387 (p : Pattern) : Int := if p 141 then d6386 p else d6382 p
theorem agree6387 (p q : Pattern) (h : Agree support p q) : d6387 p = d6387 q := by
  simp only [d6387, h 141 (by decide), agree6386 p q h, agree6382 p q h]
theorem nonnegative6387 (p : Pattern) : 0 ≤ d6387 p :=
  nonnegative_ite (p 141) (nonnegative6386 p) (nonnegative6382 p)
def d6388 (p : Pattern) : Int := if p 138 then d6387 p else d6377 p
theorem agree6388 (p q : Pattern) (h : Agree support p q) : d6388 p = d6388 q := by
  simp only [d6388, h 138 (by decide), agree6387 p q h, agree6377 p q h]
theorem nonnegative6388 (p : Pattern) : 0 ≤ d6388 p :=
  nonnegative_ite (p 138) (nonnegative6387 p) (nonnegative6377 p)
def d6389 (p : Pattern) : Int := if p 163 then d6362 p else d6334 p
theorem agree6389 (p q : Pattern) (h : Agree support p q) : d6389 p = d6389 q := by
  simp only [d6389, h 163 (by decide), agree6362 p q h, agree6334 p q h]
theorem nonnegative6389 (p : Pattern) : 0 ≤ d6389 p :=
  nonnegative_ite (p 163) (nonnegative6362 p) (nonnegative6334 p)
def d6390 (p : Pattern) : Int := if p 162 then d6363 p else d6389 p
theorem agree6390 (p q : Pattern) (h : Agree support p q) : d6390 p = d6390 q := by
  simp only [d6390, h 162 (by decide), agree6363 p q h, agree6389 p q h]
theorem nonnegative6390 (p : Pattern) : 0 ≤ d6390 p :=
  nonnegative_ite (p 162) (nonnegative6363 p) (nonnegative6389 p)
def d6391 (p : Pattern) : Int := if p 162 then d12 p else d6363 p
theorem agree6391 (p q : Pattern) (h : Agree support p q) : d6391 p = d6391 q := by
  simp only [d6391, h 162 (by decide), agree12 p q h, agree6363 p q h]
theorem nonnegative6391 (p : Pattern) : 0 ≤ d6391 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6363 p)
def d6392 (p : Pattern) : Int := if p 161 then d6391 p else d6390 p
theorem agree6392 (p q : Pattern) (h : Agree support p q) : d6392 p = d6392 q := by
  simp only [d6392, h 161 (by decide), agree6391 p q h, agree6390 p q h]
theorem nonnegative6392 (p : Pattern) : 0 ≤ d6392 p :=
  nonnegative_ite (p 161) (nonnegative6391 p) (nonnegative6390 p)
def d6393 (p : Pattern) : Int := if p 161 then d12 p else d6391 p
theorem agree6393 (p q : Pattern) (h : Agree support p q) : d6393 p = d6393 q := by
  simp only [d6393, h 161 (by decide), agree12 p q h, agree6391 p q h]
theorem nonnegative6393 (p : Pattern) : 0 ≤ d6393 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6391 p)
def d6394 (p : Pattern) : Int := if p 160 then d6393 p else d6392 p
theorem agree6394 (p q : Pattern) (h : Agree support p q) : d6394 p = d6394 q := by
  simp only [d6394, h 160 (by decide), agree6393 p q h, agree6392 p q h]
theorem nonnegative6394 (p : Pattern) : 0 ≤ d6394 p :=
  nonnegative_ite (p 160) (nonnegative6393 p) (nonnegative6392 p)
def d6395 (p : Pattern) : Int := if p 160 then d12 p else d6393 p
theorem agree6395 (p q : Pattern) (h : Agree support p q) : d6395 p = d6395 q := by
  simp only [d6395, h 160 (by decide), agree12 p q h, agree6393 p q h]
theorem nonnegative6395 (p : Pattern) : 0 ≤ d6395 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative6393 p)
def d6396 (p : Pattern) : Int := if p 141 then d6395 p else d6394 p
theorem agree6396 (p q : Pattern) (h : Agree support p q) : d6396 p = d6396 q := by
  simp only [d6396, h 141 (by decide), agree6395 p q h, agree6394 p q h]
theorem nonnegative6396 (p : Pattern) : 0 ≤ d6396 p :=
  nonnegative_ite (p 141) (nonnegative6395 p) (nonnegative6394 p)
def d6397 (p : Pattern) : Int := if p 138 then d6396 p else d6387 p
theorem agree6397 (p q : Pattern) (h : Agree support p q) : d6397 p = d6397 q := by
  simp only [d6397, h 138 (by decide), agree6396 p q h, agree6387 p q h]
theorem nonnegative6397 (p : Pattern) : 0 ≤ d6397 p :=
  nonnegative_ite (p 138) (nonnegative6396 p) (nonnegative6387 p)
def d6398 (p : Pattern) : Int := if p 116 then d6397 p else d6388 p
theorem agree6398 (p q : Pattern) (h : Agree support p q) : d6398 p = d6398 q := by
  simp only [d6398, h 116 (by decide), agree6397 p q h, agree6388 p q h]
theorem nonnegative6398 (p : Pattern) : 0 ≤ d6398 p :=
  nonnegative_ite (p 116) (nonnegative6397 p) (nonnegative6388 p)
def d6399 (p : Pattern) : Int := if p 138 then d12 p else d6387 p
theorem agree6399 (p q : Pattern) (h : Agree support p q) : d6399 p = d6399 q := by
  simp only [d6399, h 138 (by decide), agree12 p q h, agree6387 p q h]
theorem nonnegative6399 (p : Pattern) : 0 ≤ d6399 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6387 p)
def d6400 (p : Pattern) : Int := if p 116 then d6399 p else d6388 p
theorem agree6400 (p q : Pattern) (h : Agree support p q) : d6400 p = d6400 q := by
  simp only [d6400, h 116 (by decide), agree6399 p q h, agree6388 p q h]
theorem nonnegative6400 (p : Pattern) : 0 ≤ d6400 p :=
  nonnegative_ite (p 116) (nonnegative6399 p) (nonnegative6388 p)
def d6401 (p : Pattern) : Int := if p 115 then d6400 p else d6398 p
theorem agree6401 (p q : Pattern) (h : Agree support p q) : d6401 p = d6401 q := by
  simp only [d6401, h 115 (by decide), agree6400 p q h, agree6398 p q h]
theorem nonnegative6401 (p : Pattern) : 0 ≤ d6401 p :=
  nonnegative_ite (p 115) (nonnegative6400 p) (nonnegative6398 p)
def d6402 (p : Pattern) : Int := if p 204 then d12 p else d1 p
theorem agree6402 (p q : Pattern) (h : Agree support p q) : d6402 p = d6402 q := by
  simp only [d6402, h 204 (by decide), agree12 p q h, agree1 p q h]
theorem nonnegative6402 (p : Pattern) : 0 ≤ d6402 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1 p)
def d6403 (p : Pattern) : Int := if p 182 then d6402 p else d1 p
theorem agree6403 (p q : Pattern) (h : Agree support p q) : d6403 p = d6403 q := by
  simp only [d6403, h 182 (by decide), agree6402 p q h, agree1 p q h]
theorem nonnegative6403 (p : Pattern) : 0 ≤ d6403 p :=
  nonnegative_ite (p 182) (nonnegative6402 p) (nonnegative1 p)
def d6404 (p : Pattern) : Int := if p 204 then d12 p else d5 p
theorem agree6404 (p q : Pattern) (h : Agree support p q) : d6404 p = d6404 q := by
  simp only [d6404, h 204 (by decide), agree12 p q h, agree5 p q h]
theorem nonnegative6404 (p : Pattern) : 0 ≤ d6404 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5 p)
def d6405 (p : Pattern) : Int := if p 182 then d6404 p else d5 p
theorem agree6405 (p q : Pattern) (h : Agree support p q) : d6405 p = d6405 q := by
  simp only [d6405, h 182 (by decide), agree6404 p q h, agree5 p q h]
theorem nonnegative6405 (p : Pattern) : 0 ≤ d6405 p :=
  nonnegative_ite (p 182) (nonnegative6404 p) (nonnegative5 p)
def d6406 (p : Pattern) : Int := if p 163 then d6405 p else d6403 p
theorem agree6406 (p q : Pattern) (h : Agree support p q) : d6406 p = d6406 q := by
  simp only [d6406, h 163 (by decide), agree6405 p q h, agree6403 p q h]
theorem nonnegative6406 (p : Pattern) : 0 ≤ d6406 p :=
  nonnegative_ite (p 163) (nonnegative6405 p) (nonnegative6403 p)
def d6407 (p : Pattern) : Int := if p 162 then d6406 p else d6403 p
theorem agree6407 (p q : Pattern) (h : Agree support p q) : d6407 p = d6407 q := by
  simp only [d6407, h 162 (by decide), agree6406 p q h, agree6403 p q h]
theorem nonnegative6407 (p : Pattern) : 0 ≤ d6407 p :=
  nonnegative_ite (p 162) (nonnegative6406 p) (nonnegative6403 p)
def d6408 (p : Pattern) : Int := if p 163 then d12 p else d6360 p
theorem agree6408 (p q : Pattern) (h : Agree support p q) : d6408 p = d6408 q := by
  simp only [d6408, h 163 (by decide), agree12 p q h, agree6360 p q h]
theorem nonnegative6408 (p : Pattern) : 0 ≤ d6408 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6360 p)
def d6409 (p : Pattern) : Int := if p 162 then d6408 p else d6406 p
theorem agree6409 (p q : Pattern) (h : Agree support p q) : d6409 p = d6409 q := by
  simp only [d6409, h 162 (by decide), agree6408 p q h, agree6406 p q h]
theorem nonnegative6409 (p : Pattern) : 0 ≤ d6409 p :=
  nonnegative_ite (p 162) (nonnegative6408 p) (nonnegative6406 p)
def d6410 (p : Pattern) : Int := if p 161 then d6409 p else d6407 p
theorem agree6410 (p q : Pattern) (h : Agree support p q) : d6410 p = d6410 q := by
  simp only [d6410, h 161 (by decide), agree6409 p q h, agree6407 p q h]
theorem nonnegative6410 (p : Pattern) : 0 ≤ d6410 p :=
  nonnegative_ite (p 161) (nonnegative6409 p) (nonnegative6407 p)
def d6411 (p : Pattern) : Int := if p 204 then d12 p else d3 p
theorem agree6411 (p q : Pattern) (h : Agree support p q) : d6411 p = d6411 q := by
  simp only [d6411, h 204 (by decide), agree12 p q h, agree3 p q h]
theorem nonnegative6411 (p : Pattern) : 0 ≤ d6411 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3 p)
def d6412 (p : Pattern) : Int := if p 182 then d6411 p else d1 p
theorem agree6412 (p q : Pattern) (h : Agree support p q) : d6412 p = d6412 q := by
  simp only [d6412, h 182 (by decide), agree6411 p q h, agree1 p q h]
theorem nonnegative6412 (p : Pattern) : 0 ≤ d6412 p :=
  nonnegative_ite (p 182) (nonnegative6411 p) (nonnegative1 p)
def d6413 (p : Pattern) : Int := if p 204 then d12 p else d7 p
theorem agree6413 (p q : Pattern) (h : Agree support p q) : d6413 p = d6413 q := by
  simp only [d6413, h 204 (by decide), agree12 p q h, agree7 p q h]
theorem nonnegative6413 (p : Pattern) : 0 ≤ d6413 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7 p)
def d6414 (p : Pattern) : Int := if p 182 then d6413 p else d1 p
theorem agree6414 (p q : Pattern) (h : Agree support p q) : d6414 p = d6414 q := by
  simp only [d6414, h 182 (by decide), agree6413 p q h, agree1 p q h]
theorem nonnegative6414 (p : Pattern) : 0 ≤ d6414 p :=
  nonnegative_ite (p 182) (nonnegative6413 p) (nonnegative1 p)
def d6415 (p : Pattern) : Int := if p 163 then d6414 p else d6412 p
theorem agree6415 (p q : Pattern) (h : Agree support p q) : d6415 p = d6415 q := by
  simp only [d6415, h 163 (by decide), agree6414 p q h, agree6412 p q h]
theorem nonnegative6415 (p : Pattern) : 0 ≤ d6415 p :=
  nonnegative_ite (p 163) (nonnegative6414 p) (nonnegative6412 p)
def d6416 (p : Pattern) : Int := if p 182 then d12 p else d1 p
theorem agree6416 (p q : Pattern) (h : Agree support p q) : d6416 p = d6416 q := by
  simp only [d6416, h 182 (by decide), agree12 p q h, agree1 p q h]
theorem nonnegative6416 (p : Pattern) : 0 ≤ d6416 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1 p)
def d6417 (p : Pattern) : Int := if p 182 then d12 p else d5 p
theorem agree6417 (p q : Pattern) (h : Agree support p q) : d6417 p = d6417 q := by
  simp only [d6417, h 182 (by decide), agree12 p q h, agree5 p q h]
theorem nonnegative6417 (p : Pattern) : 0 ≤ d6417 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5 p)
def d6418 (p : Pattern) : Int := if p 163 then d6417 p else d6416 p
theorem agree6418 (p q : Pattern) (h : Agree support p q) : d6418 p = d6418 q := by
  simp only [d6418, h 163 (by decide), agree6417 p q h, agree6416 p q h]
theorem nonnegative6418 (p : Pattern) : 0 ≤ d6418 p :=
  nonnegative_ite (p 163) (nonnegative6417 p) (nonnegative6416 p)
def d6419 (p : Pattern) : Int := if p 162 then d6418 p else d6415 p
theorem agree6419 (p q : Pattern) (h : Agree support p q) : d6419 p = d6419 q := by
  simp only [d6419, h 162 (by decide), agree6418 p q h, agree6415 p q h]
theorem nonnegative6419 (p : Pattern) : 0 ≤ d6419 p :=
  nonnegative_ite (p 162) (nonnegative6418 p) (nonnegative6415 p)
def d6420 (p : Pattern) : Int := if p 163 then d12 p else d6370 p
theorem agree6420 (p q : Pattern) (h : Agree support p q) : d6420 p = d6420 q := by
  simp only [d6420, h 163 (by decide), agree12 p q h, agree6370 p q h]
theorem nonnegative6420 (p : Pattern) : 0 ≤ d6420 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6370 p)
def d6421 (p : Pattern) : Int := if p 162 then d6420 p else d6418 p
theorem agree6421 (p q : Pattern) (h : Agree support p q) : d6421 p = d6421 q := by
  simp only [d6421, h 162 (by decide), agree6420 p q h, agree6418 p q h]
theorem nonnegative6421 (p : Pattern) : 0 ≤ d6421 p :=
  nonnegative_ite (p 162) (nonnegative6420 p) (nonnegative6418 p)
def d6422 (p : Pattern) : Int := if p 161 then d6421 p else d6419 p
theorem agree6422 (p q : Pattern) (h : Agree support p q) : d6422 p = d6422 q := by
  simp only [d6422, h 161 (by decide), agree6421 p q h, agree6419 p q h]
theorem nonnegative6422 (p : Pattern) : 0 ≤ d6422 p :=
  nonnegative_ite (p 161) (nonnegative6421 p) (nonnegative6419 p)
def d6423 (p : Pattern) : Int := if p 160 then d6422 p else d6410 p
theorem agree6423 (p q : Pattern) (h : Agree support p q) : d6423 p = d6423 q := by
  simp only [d6423, h 160 (by decide), agree6422 p q h, agree6410 p q h]
theorem nonnegative6423 (p : Pattern) : 0 ≤ d6423 p :=
  nonnegative_ite (p 160) (nonnegative6422 p) (nonnegative6410 p)
def d6424 (p : Pattern) : Int := if p 182 then d6411 p else d3 p
theorem agree6424 (p q : Pattern) (h : Agree support p q) : d6424 p = d6424 q := by
  simp only [d6424, h 182 (by decide), agree6411 p q h, agree3 p q h]
theorem nonnegative6424 (p : Pattern) : 0 ≤ d6424 p :=
  nonnegative_ite (p 182) (nonnegative6411 p) (nonnegative3 p)
def d6425 (p : Pattern) : Int := if p 163 then d6424 p else d6403 p
theorem agree6425 (p q : Pattern) (h : Agree support p q) : d6425 p = d6425 q := by
  simp only [d6425, h 163 (by decide), agree6424 p q h, agree6403 p q h]
theorem nonnegative6425 (p : Pattern) : 0 ≤ d6425 p :=
  nonnegative_ite (p 163) (nonnegative6424 p) (nonnegative6403 p)
def d6426 (p : Pattern) : Int := if p 163 then d6360 p else d6405 p
theorem agree6426 (p q : Pattern) (h : Agree support p q) : d6426 p = d6426 q := by
  simp only [d6426, h 163 (by decide), agree6360 p q h, agree6405 p q h]
theorem nonnegative6426 (p : Pattern) : 0 ≤ d6426 p :=
  nonnegative_ite (p 163) (nonnegative6360 p) (nonnegative6405 p)
def d6427 (p : Pattern) : Int := if p 162 then d6426 p else d6425 p
theorem agree6427 (p q : Pattern) (h : Agree support p q) : d6427 p = d6427 q := by
  simp only [d6427, h 162 (by decide), agree6426 p q h, agree6425 p q h]
theorem nonnegative6427 (p : Pattern) : 0 ≤ d6427 p :=
  nonnegative_ite (p 162) (nonnegative6426 p) (nonnegative6425 p)
def d6428 (p : Pattern) : Int := if p 163 then d6362 p else d6405 p
theorem agree6428 (p q : Pattern) (h : Agree support p q) : d6428 p = d6428 q := by
  simp only [d6428, h 163 (by decide), agree6362 p q h, agree6405 p q h]
theorem nonnegative6428 (p : Pattern) : 0 ≤ d6428 p :=
  nonnegative_ite (p 163) (nonnegative6362 p) (nonnegative6405 p)
def d6429 (p : Pattern) : Int := if p 162 then d12 p else d6428 p
theorem agree6429 (p q : Pattern) (h : Agree support p q) : d6429 p = d6429 q := by
  simp only [d6429, h 162 (by decide), agree12 p q h, agree6428 p q h]
theorem nonnegative6429 (p : Pattern) : 0 ≤ d6429 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6428 p)
def d6430 (p : Pattern) : Int := if p 161 then d6429 p else d6427 p
theorem agree6430 (p q : Pattern) (h : Agree support p q) : d6430 p = d6430 q := by
  simp only [d6430, h 161 (by decide), agree6429 p q h, agree6427 p q h]
theorem nonnegative6430 (p : Pattern) : 0 ≤ d6430 p :=
  nonnegative_ite (p 161) (nonnegative6429 p) (nonnegative6427 p)
def d6431 (p : Pattern) : Int := if p 182 then d12 p else d3 p
theorem agree6431 (p q : Pattern) (h : Agree support p q) : d6431 p = d6431 q := by
  simp only [d6431, h 182 (by decide), agree12 p q h, agree3 p q h]
theorem nonnegative6431 (p : Pattern) : 0 ≤ d6431 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3 p)
def d6432 (p : Pattern) : Int := if p 163 then d6431 p else d6414 p
theorem agree6432 (p q : Pattern) (h : Agree support p q) : d6432 p = d6432 q := by
  simp only [d6432, h 163 (by decide), agree6431 p q h, agree6414 p q h]
theorem nonnegative6432 (p : Pattern) : 0 ≤ d6432 p :=
  nonnegative_ite (p 163) (nonnegative6431 p) (nonnegative6414 p)
def d6433 (p : Pattern) : Int := if p 163 then d6370 p else d6417 p
theorem agree6433 (p q : Pattern) (h : Agree support p q) : d6433 p = d6433 q := by
  simp only [d6433, h 163 (by decide), agree6370 p q h, agree6417 p q h]
theorem nonnegative6433 (p : Pattern) : 0 ≤ d6433 p :=
  nonnegative_ite (p 163) (nonnegative6370 p) (nonnegative6417 p)
def d6434 (p : Pattern) : Int := if p 162 then d6433 p else d6432 p
theorem agree6434 (p q : Pattern) (h : Agree support p q) : d6434 p = d6434 q := by
  simp only [d6434, h 162 (by decide), agree6433 p q h, agree6432 p q h]
theorem nonnegative6434 (p : Pattern) : 0 ≤ d6434 p :=
  nonnegative_ite (p 162) (nonnegative6433 p) (nonnegative6432 p)
def d6435 (p : Pattern) : Int := if p 163 then d6372 p else d6417 p
theorem agree6435 (p q : Pattern) (h : Agree support p q) : d6435 p = d6435 q := by
  simp only [d6435, h 163 (by decide), agree6372 p q h, agree6417 p q h]
theorem nonnegative6435 (p : Pattern) : 0 ≤ d6435 p :=
  nonnegative_ite (p 163) (nonnegative6372 p) (nonnegative6417 p)
def d6436 (p : Pattern) : Int := if p 162 then d12 p else d6435 p
theorem agree6436 (p q : Pattern) (h : Agree support p q) : d6436 p = d6436 q := by
  simp only [d6436, h 162 (by decide), agree12 p q h, agree6435 p q h]
theorem nonnegative6436 (p : Pattern) : 0 ≤ d6436 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6435 p)
def d6437 (p : Pattern) : Int := if p 161 then d6436 p else d6434 p
theorem agree6437 (p q : Pattern) (h : Agree support p q) : d6437 p = d6437 q := by
  simp only [d6437, h 161 (by decide), agree6436 p q h, agree6434 p q h]
theorem nonnegative6437 (p : Pattern) : 0 ≤ d6437 p :=
  nonnegative_ite (p 161) (nonnegative6436 p) (nonnegative6434 p)
def d6438 (p : Pattern) : Int := if p 160 then d6437 p else d6430 p
theorem agree6438 (p q : Pattern) (h : Agree support p q) : d6438 p = d6438 q := by
  simp only [d6438, h 160 (by decide), agree6437 p q h, agree6430 p q h]
theorem nonnegative6438 (p : Pattern) : 0 ≤ d6438 p :=
  nonnegative_ite (p 160) (nonnegative6437 p) (nonnegative6430 p)
def d6439 (p : Pattern) : Int := if p 141 then d6438 p else d6423 p
theorem agree6439 (p q : Pattern) (h : Agree support p q) : d6439 p = d6439 q := by
  simp only [d6439, h 141 (by decide), agree6438 p q h, agree6423 p q h]
theorem nonnegative6439 (p : Pattern) : 0 ≤ d6439 p :=
  nonnegative_ite (p 141) (nonnegative6438 p) (nonnegative6423 p)
def d6440 (p : Pattern) : Int := if p 182 then d6413 p else d7 p
theorem agree6440 (p q : Pattern) (h : Agree support p q) : d6440 p = d6440 q := by
  simp only [d6440, h 182 (by decide), agree6413 p q h, agree7 p q h]
theorem nonnegative6440 (p : Pattern) : 0 ≤ d6440 p :=
  nonnegative_ite (p 182) (nonnegative6413 p) (nonnegative7 p)
def d6441 (p : Pattern) : Int := if p 163 then d6440 p else d6424 p
theorem agree6441 (p q : Pattern) (h : Agree support p q) : d6441 p = d6441 q := by
  simp only [d6441, h 163 (by decide), agree6440 p q h, agree6424 p q h]
theorem nonnegative6441 (p : Pattern) : 0 ≤ d6441 p :=
  nonnegative_ite (p 163) (nonnegative6440 p) (nonnegative6424 p)
def d6442 (p : Pattern) : Int := if p 162 then d12 p else d6441 p
theorem agree6442 (p q : Pattern) (h : Agree support p q) : d6442 p = d6442 q := by
  simp only [d6442, h 162 (by decide), agree12 p q h, agree6441 p q h]
theorem nonnegative6442 (p : Pattern) : 0 ≤ d6442 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6441 p)
def d6443 (p : Pattern) : Int := if p 161 then d12 p else d6442 p
theorem agree6443 (p q : Pattern) (h : Agree support p q) : d6443 p = d6443 q := by
  simp only [d6443, h 161 (by decide), agree12 p q h, agree6442 p q h]
theorem nonnegative6443 (p : Pattern) : 0 ≤ d6443 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6442 p)
def d6444 (p : Pattern) : Int := if p 160 then d6443 p else d6410 p
theorem agree6444 (p q : Pattern) (h : Agree support p q) : d6444 p = d6444 q := by
  simp only [d6444, h 160 (by decide), agree6443 p q h, agree6410 p q h]
theorem nonnegative6444 (p : Pattern) : 0 ≤ d6444 p :=
  nonnegative_ite (p 160) (nonnegative6443 p) (nonnegative6410 p)
def d6445 (p : Pattern) : Int := if p 163 then d12 p else d6440 p
theorem agree6445 (p q : Pattern) (h : Agree support p q) : d6445 p = d6445 q := by
  simp only [d6445, h 163 (by decide), agree12 p q h, agree6440 p q h]
theorem nonnegative6445 (p : Pattern) : 0 ≤ d6445 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6440 p)
def d6446 (p : Pattern) : Int := if p 162 then d12 p else d6445 p
theorem agree6446 (p q : Pattern) (h : Agree support p q) : d6446 p = d6446 q := by
  simp only [d6446, h 162 (by decide), agree12 p q h, agree6445 p q h]
theorem nonnegative6446 (p : Pattern) : 0 ≤ d6446 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6445 p)
def d6447 (p : Pattern) : Int := if p 161 then d12 p else d6446 p
theorem agree6447 (p q : Pattern) (h : Agree support p q) : d6447 p = d6447 q := by
  simp only [d6447, h 161 (by decide), agree12 p q h, agree6446 p q h]
theorem nonnegative6447 (p : Pattern) : 0 ≤ d6447 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6446 p)
def d6448 (p : Pattern) : Int := if p 160 then d6447 p else d6430 p
theorem agree6448 (p q : Pattern) (h : Agree support p q) : d6448 p = d6448 q := by
  simp only [d6448, h 160 (by decide), agree6447 p q h, agree6430 p q h]
theorem nonnegative6448 (p : Pattern) : 0 ≤ d6448 p :=
  nonnegative_ite (p 160) (nonnegative6447 p) (nonnegative6430 p)
def d6449 (p : Pattern) : Int := if p 141 then d6448 p else d6444 p
theorem agree6449 (p q : Pattern) (h : Agree support p q) : d6449 p = d6449 q := by
  simp only [d6449, h 141 (by decide), agree6448 p q h, agree6444 p q h]
theorem nonnegative6449 (p : Pattern) : 0 ≤ d6449 p :=
  nonnegative_ite (p 141) (nonnegative6448 p) (nonnegative6444 p)
def d6450 (p : Pattern) : Int := if p 138 then d6449 p else d6439 p
theorem agree6450 (p q : Pattern) (h : Agree support p q) : d6450 p = d6450 q := by
  simp only [d6450, h 138 (by decide), agree6449 p q h, agree6439 p q h]
theorem nonnegative6450 (p : Pattern) : 0 ≤ d6450 p :=
  nonnegative_ite (p 138) (nonnegative6449 p) (nonnegative6439 p)
def d6451 (p : Pattern) : Int := if p 162 then d12 p else d6408 p
theorem agree6451 (p q : Pattern) (h : Agree support p q) : d6451 p = d6451 q := by
  simp only [d6451, h 162 (by decide), agree12 p q h, agree6408 p q h]
theorem nonnegative6451 (p : Pattern) : 0 ≤ d6451 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6408 p)
def d6452 (p : Pattern) : Int := if p 161 then d12 p else d6451 p
theorem agree6452 (p q : Pattern) (h : Agree support p q) : d6452 p = d6452 q := by
  simp only [d6452, h 161 (by decide), agree12 p q h, agree6451 p q h]
theorem nonnegative6452 (p : Pattern) : 0 ≤ d6452 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6451 p)
def d6453 (p : Pattern) : Int := if p 160 then d12 p else d6452 p
theorem agree6453 (p q : Pattern) (h : Agree support p q) : d6453 p = d6453 q := by
  simp only [d6453, h 160 (by decide), agree12 p q h, agree6452 p q h]
theorem nonnegative6453 (p : Pattern) : 0 ≤ d6453 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative6452 p)
def d6454 (p : Pattern) : Int := if p 141 then d12 p else d6453 p
theorem agree6454 (p q : Pattern) (h : Agree support p q) : d6454 p = d6454 q := by
  simp only [d6454, h 141 (by decide), agree12 p q h, agree6453 p q h]
theorem nonnegative6454 (p : Pattern) : 0 ≤ d6454 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative6453 p)
def d6455 (p : Pattern) : Int := if p 138 then d6454 p else d6449 p
theorem agree6455 (p q : Pattern) (h : Agree support p q) : d6455 p = d6455 q := by
  simp only [d6455, h 138 (by decide), agree6454 p q h, agree6449 p q h]
theorem nonnegative6455 (p : Pattern) : 0 ≤ d6455 p :=
  nonnegative_ite (p 138) (nonnegative6454 p) (nonnegative6449 p)
def d6456 (p : Pattern) : Int := if p 116 then d6455 p else d6450 p
theorem agree6456 (p q : Pattern) (h : Agree support p q) : d6456 p = d6456 q := by
  simp only [d6456, h 116 (by decide), agree6455 p q h, agree6450 p q h]
theorem nonnegative6456 (p : Pattern) : 0 ≤ d6456 p :=
  nonnegative_ite (p 116) (nonnegative6455 p) (nonnegative6450 p)
def d6457 (p : Pattern) : Int := if p 138 then d12 p else d6449 p
theorem agree6457 (p q : Pattern) (h : Agree support p q) : d6457 p = d6457 q := by
  simp only [d6457, h 138 (by decide), agree12 p q h, agree6449 p q h]
theorem nonnegative6457 (p : Pattern) : 0 ≤ d6457 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6449 p)
def d6458 (p : Pattern) : Int := if p 116 then d6457 p else d6450 p
theorem agree6458 (p q : Pattern) (h : Agree support p q) : d6458 p = d6458 q := by
  simp only [d6458, h 116 (by decide), agree6457 p q h, agree6450 p q h]
theorem nonnegative6458 (p : Pattern) : 0 ≤ d6458 p :=
  nonnegative_ite (p 116) (nonnegative6457 p) (nonnegative6450 p)
def d6459 (p : Pattern) : Int := if p 115 then d6458 p else d6456 p
theorem agree6459 (p q : Pattern) (h : Agree support p q) : d6459 p = d6459 q := by
  simp only [d6459, h 115 (by decide), agree6458 p q h, agree6456 p q h]
theorem nonnegative6459 (p : Pattern) : 0 ≤ d6459 p :=
  nonnegative_ite (p 115) (nonnegative6458 p) (nonnegative6456 p)
def d6460 (p : Pattern) : Int := if p 71 then d6459 p else d6401 p
theorem agree6460 (p q : Pattern) (h : Agree support p q) : d6460 p = d6460 q := by
  simp only [d6460, h 71 (by decide), agree6459 p q h, agree6401 p q h]
theorem nonnegative6460 (p : Pattern) : 0 ≤ d6460 p :=
  nonnegative_ite (p 71) (nonnegative6459 p) (nonnegative6401 p)
def d6461 (p : Pattern) : Int := if p 49 then d6460 p else d6401 p
theorem agree6461 (p q : Pattern) (h : Agree support p q) : d6461 p = d6461 q := by
  simp only [d6461, h 49 (by decide), agree6460 p q h, agree6401 p q h]
theorem nonnegative6461 (p : Pattern) : 0 ≤ d6461 p :=
  nonnegative_ite (p 49) (nonnegative6460 p) (nonnegative6401 p)
def d6462 (p : Pattern) : Int := if p 182 then d6340 p else d2 p
theorem agree6462 (p q : Pattern) (h : Agree support p q) : d6462 p = d6462 q := by
  simp only [d6462, h 182 (by decide), agree6340 p q h, agree2 p q h]
theorem nonnegative6462 (p : Pattern) : 0 ≤ d6462 p :=
  nonnegative_ite (p 182) (nonnegative6340 p) (nonnegative2 p)
def d6463 (p : Pattern) : Int := if p 163 then d6462 p else d6355 p
theorem agree6463 (p q : Pattern) (h : Agree support p q) : d6463 p = d6463 q := by
  simp only [d6463, h 163 (by decide), agree6462 p q h, agree6355 p q h]
theorem nonnegative6463 (p : Pattern) : 0 ≤ d6463 p :=
  nonnegative_ite (p 163) (nonnegative6462 p) (nonnegative6355 p)
def d6464 (p : Pattern) : Int := if p 182 then d6343 p else d2 p
theorem agree6464 (p q : Pattern) (h : Agree support p q) : d6464 p = d6464 q := by
  simp only [d6464, h 182 (by decide), agree6343 p q h, agree2 p q h]
theorem nonnegative6464 (p : Pattern) : 0 ≤ d6464 p :=
  nonnegative_ite (p 182) (nonnegative6343 p) (nonnegative2 p)
def d6465 (p : Pattern) : Int := if p 182 then d12 p else d6 p
theorem agree6465 (p q : Pattern) (h : Agree support p q) : d6465 p = d6465 q := by
  simp only [d6465, h 182 (by decide), agree12 p q h, agree6 p q h]
theorem nonnegative6465 (p : Pattern) : 0 ≤ d6465 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6 p)
def d6466 (p : Pattern) : Int := if p 163 then d6465 p else d6464 p
theorem agree6466 (p q : Pattern) (h : Agree support p q) : d6466 p = d6466 q := by
  simp only [d6466, h 163 (by decide), agree6465 p q h, agree6464 p q h]
theorem nonnegative6466 (p : Pattern) : 0 ≤ d6466 p :=
  nonnegative_ite (p 163) (nonnegative6465 p) (nonnegative6464 p)
def d6467 (p : Pattern) : Int := if p 162 then d6466 p else d6463 p
theorem agree6467 (p q : Pattern) (h : Agree support p q) : d6467 p = d6467 q := by
  simp only [d6467, h 162 (by decide), agree6466 p q h, agree6463 p q h]
theorem nonnegative6467 (p : Pattern) : 0 ≤ d6467 p :=
  nonnegative_ite (p 162) (nonnegative6466 p) (nonnegative6463 p)
def d6468 (p : Pattern) : Int := if p 163 then d6465 p else d6366 p
theorem agree6468 (p q : Pattern) (h : Agree support p q) : d6468 p = d6468 q := by
  simp only [d6468, h 163 (by decide), agree6465 p q h, agree6366 p q h]
theorem nonnegative6468 (p : Pattern) : 0 ≤ d6468 p :=
  nonnegative_ite (p 163) (nonnegative6465 p) (nonnegative6366 p)
def d6469 (p : Pattern) : Int := if p 162 then d6373 p else d6468 p
theorem agree6469 (p q : Pattern) (h : Agree support p q) : d6469 p = d6469 q := by
  simp only [d6469, h 162 (by decide), agree6373 p q h, agree6468 p q h]
theorem nonnegative6469 (p : Pattern) : 0 ≤ d6469 p :=
  nonnegative_ite (p 162) (nonnegative6373 p) (nonnegative6468 p)
def d6470 (p : Pattern) : Int := if p 161 then d6469 p else d6467 p
theorem agree6470 (p q : Pattern) (h : Agree support p q) : d6470 p = d6470 q := by
  simp only [d6470, h 161 (by decide), agree6469 p q h, agree6467 p q h]
theorem nonnegative6470 (p : Pattern) : 0 ≤ d6470 p :=
  nonnegative_ite (p 161) (nonnegative6469 p) (nonnegative6467 p)
def d6471 (p : Pattern) : Int := if p 160 then d6470 p else d6337 p
theorem agree6471 (p q : Pattern) (h : Agree support p q) : d6471 p = d6471 q := by
  simp only [d6471, h 160 (by decide), agree6470 p q h, agree6337 p q h]
theorem nonnegative6471 (p : Pattern) : 0 ≤ d6471 p :=
  nonnegative_ite (p 160) (nonnegative6470 p) (nonnegative6337 p)
def d6472 (p : Pattern) : Int := if p 163 then d6345 p else d6462 p
theorem agree6472 (p q : Pattern) (h : Agree support p q) : d6472 p = d6472 q := by
  simp only [d6472, h 163 (by decide), agree6345 p q h, agree6462 p q h]
theorem nonnegative6472 (p : Pattern) : 0 ≤ d6472 p :=
  nonnegative_ite (p 163) (nonnegative6345 p) (nonnegative6462 p)
def d6473 (p : Pattern) : Int := if p 163 then d6372 p else d6465 p
theorem agree6473 (p q : Pattern) (h : Agree support p q) : d6473 p = d6473 q := by
  simp only [d6473, h 163 (by decide), agree6372 p q h, agree6465 p q h]
theorem nonnegative6473 (p : Pattern) : 0 ≤ d6473 p :=
  nonnegative_ite (p 163) (nonnegative6372 p) (nonnegative6465 p)
def d6474 (p : Pattern) : Int := if p 162 then d6473 p else d6472 p
theorem agree6474 (p q : Pattern) (h : Agree support p q) : d6474 p = d6474 q := by
  simp only [d6474, h 162 (by decide), agree6473 p q h, agree6472 p q h]
theorem nonnegative6474 (p : Pattern) : 0 ≤ d6474 p :=
  nonnegative_ite (p 162) (nonnegative6473 p) (nonnegative6472 p)
def d6475 (p : Pattern) : Int := if p 163 then d12 p else d6465 p
theorem agree6475 (p q : Pattern) (h : Agree support p q) : d6475 p = d6475 q := by
  simp only [d6475, h 163 (by decide), agree12 p q h, agree6465 p q h]
theorem nonnegative6475 (p : Pattern) : 0 ≤ d6475 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6465 p)
def d6476 (p : Pattern) : Int := if p 162 then d12 p else d6475 p
theorem agree6476 (p q : Pattern) (h : Agree support p q) : d6476 p = d6476 q := by
  simp only [d6476, h 162 (by decide), agree12 p q h, agree6475 p q h]
theorem nonnegative6476 (p : Pattern) : 0 ≤ d6476 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6475 p)
def d6477 (p : Pattern) : Int := if p 161 then d6476 p else d6474 p
theorem agree6477 (p q : Pattern) (h : Agree support p q) : d6477 p = d6477 q := by
  simp only [d6477, h 161 (by decide), agree6476 p q h, agree6474 p q h]
theorem nonnegative6477 (p : Pattern) : 0 ≤ d6477 p :=
  nonnegative_ite (p 161) (nonnegative6476 p) (nonnegative6474 p)
def d6478 (p : Pattern) : Int := if p 160 then d6477 p else d6365 p
theorem agree6478 (p q : Pattern) (h : Agree support p q) : d6478 p = d6478 q := by
  simp only [d6478, h 160 (by decide), agree6477 p q h, agree6365 p q h]
theorem nonnegative6478 (p : Pattern) : 0 ≤ d6478 p :=
  nonnegative_ite (p 160) (nonnegative6477 p) (nonnegative6365 p)
def d6479 (p : Pattern) : Int := if p 141 then d6478 p else d6471 p
theorem agree6479 (p q : Pattern) (h : Agree support p q) : d6479 p = d6479 q := by
  simp only [d6479, h 141 (by decide), agree6478 p q h, agree6471 p q h]
theorem nonnegative6479 (p : Pattern) : 0 ≤ d6479 p :=
  nonnegative_ite (p 141) (nonnegative6478 p) (nonnegative6471 p)
end NetHack.Sokoban22Refined85
