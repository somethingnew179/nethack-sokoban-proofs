/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes44
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d5400 (p : Pattern) : Int := if p 138 then d12 p else d5392 p
theorem agree5400 (p q : Pattern) (h : Agree support p q) : d5400 p = d5400 q := by
  simp only [d5400, h 138 (by decide), agree12 p q h, agree5392 p q h]
theorem nonnegative5400 (p : Pattern) : 0 ≤ d5400 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5392 p)
def d5401 (p : Pattern) : Int := if p 116 then d5400 p else d5393 p
theorem agree5401 (p q : Pattern) (h : Agree support p q) : d5401 p = d5401 q := by
  simp only [d5401, h 116 (by decide), agree5400 p q h, agree5393 p q h]
theorem nonnegative5401 (p : Pattern) : 0 ≤ d5401 p :=
  nonnegative_ite (p 116) (nonnegative5400 p) (nonnegative5393 p)
def d5402 (p : Pattern) : Int := if p 115 then d5401 p else d5399 p
theorem agree5402 (p q : Pattern) (h : Agree support p q) : d5402 p = d5402 q := by
  simp only [d5402, h 115 (by decide), agree5401 p q h, agree5399 p q h]
theorem nonnegative5402 (p : Pattern) : 0 ≤ d5402 p :=
  nonnegative_ite (p 115) (nonnegative5401 p) (nonnegative5399 p)
def d5403 (p : Pattern) : Int := if p 71 then d5402 p else d5344 p
theorem agree5403 (p q : Pattern) (h : Agree support p q) : d5403 p = d5403 q := by
  simp only [d5403, h 71 (by decide), agree5402 p q h, agree5344 p q h]
theorem nonnegative5403 (p : Pattern) : 0 ≤ d5403 p :=
  nonnegative_ite (p 71) (nonnegative5402 p) (nonnegative5344 p)
def d5404 (p : Pattern) : Int := if p 49 then d5403 p else d5344 p
theorem agree5404 (p q : Pattern) (h : Agree support p q) : d5404 p = d5404 q := by
  simp only [d5404, h 49 (by decide), agree5403 p q h, agree5344 p q h]
theorem nonnegative5404 (p : Pattern) : 0 ≤ d5404 p :=
  nonnegative_ite (p 49) (nonnegative5403 p) (nonnegative5344 p)
def d5405 (p : Pattern) : Int := if p 182 then d5283 p else d30 p
theorem agree5405 (p q : Pattern) (h : Agree support p q) : d5405 p = d5405 q := by
  simp only [d5405, h 182 (by decide), agree5283 p q h, agree30 p q h]
theorem nonnegative5405 (p : Pattern) : 0 ≤ d5405 p :=
  nonnegative_ite (p 182) (nonnegative5283 p) (nonnegative30 p)
def d5406 (p : Pattern) : Int := if p 163 then d5405 p else d5298 p
theorem agree5406 (p q : Pattern) (h : Agree support p q) : d5406 p = d5406 q := by
  simp only [d5406, h 163 (by decide), agree5405 p q h, agree5298 p q h]
theorem nonnegative5406 (p : Pattern) : 0 ≤ d5406 p :=
  nonnegative_ite (p 163) (nonnegative5405 p) (nonnegative5298 p)
def d5407 (p : Pattern) : Int := if p 182 then d5286 p else d30 p
theorem agree5407 (p q : Pattern) (h : Agree support p q) : d5407 p = d5407 q := by
  simp only [d5407, h 182 (by decide), agree5286 p q h, agree30 p q h]
theorem nonnegative5407 (p : Pattern) : 0 ≤ d5407 p :=
  nonnegative_ite (p 182) (nonnegative5286 p) (nonnegative30 p)
def d5408 (p : Pattern) : Int := if p 182 then d12 p else d34 p
theorem agree5408 (p q : Pattern) (h : Agree support p q) : d5408 p = d5408 q := by
  simp only [d5408, h 182 (by decide), agree12 p q h, agree34 p q h]
theorem nonnegative5408 (p : Pattern) : 0 ≤ d5408 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative34 p)
def d5409 (p : Pattern) : Int := if p 163 then d5408 p else d5407 p
theorem agree5409 (p q : Pattern) (h : Agree support p q) : d5409 p = d5409 q := by
  simp only [d5409, h 163 (by decide), agree5408 p q h, agree5407 p q h]
theorem nonnegative5409 (p : Pattern) : 0 ≤ d5409 p :=
  nonnegative_ite (p 163) (nonnegative5408 p) (nonnegative5407 p)
def d5410 (p : Pattern) : Int := if p 162 then d5409 p else d5406 p
theorem agree5410 (p q : Pattern) (h : Agree support p q) : d5410 p = d5410 q := by
  simp only [d5410, h 162 (by decide), agree5409 p q h, agree5406 p q h]
theorem nonnegative5410 (p : Pattern) : 0 ≤ d5410 p :=
  nonnegative_ite (p 162) (nonnegative5409 p) (nonnegative5406 p)
def d5411 (p : Pattern) : Int := if p 163 then d5408 p else d5309 p
theorem agree5411 (p q : Pattern) (h : Agree support p q) : d5411 p = d5411 q := by
  simp only [d5411, h 163 (by decide), agree5408 p q h, agree5309 p q h]
theorem nonnegative5411 (p : Pattern) : 0 ≤ d5411 p :=
  nonnegative_ite (p 163) (nonnegative5408 p) (nonnegative5309 p)
def d5412 (p : Pattern) : Int := if p 162 then d5316 p else d5411 p
theorem agree5412 (p q : Pattern) (h : Agree support p q) : d5412 p = d5412 q := by
  simp only [d5412, h 162 (by decide), agree5316 p q h, agree5411 p q h]
theorem nonnegative5412 (p : Pattern) : 0 ≤ d5412 p :=
  nonnegative_ite (p 162) (nonnegative5316 p) (nonnegative5411 p)
def d5413 (p : Pattern) : Int := if p 161 then d5412 p else d5410 p
theorem agree5413 (p q : Pattern) (h : Agree support p q) : d5413 p = d5413 q := by
  simp only [d5413, h 161 (by decide), agree5412 p q h, agree5410 p q h]
theorem nonnegative5413 (p : Pattern) : 0 ≤ d5413 p :=
  nonnegative_ite (p 161) (nonnegative5412 p) (nonnegative5410 p)
def d5414 (p : Pattern) : Int := if p 160 then d5413 p else d5280 p
theorem agree5414 (p q : Pattern) (h : Agree support p q) : d5414 p = d5414 q := by
  simp only [d5414, h 160 (by decide), agree5413 p q h, agree5280 p q h]
theorem nonnegative5414 (p : Pattern) : 0 ≤ d5414 p :=
  nonnegative_ite (p 160) (nonnegative5413 p) (nonnegative5280 p)
def d5415 (p : Pattern) : Int := if p 163 then d5288 p else d5405 p
theorem agree5415 (p q : Pattern) (h : Agree support p q) : d5415 p = d5415 q := by
  simp only [d5415, h 163 (by decide), agree5288 p q h, agree5405 p q h]
theorem nonnegative5415 (p : Pattern) : 0 ≤ d5415 p :=
  nonnegative_ite (p 163) (nonnegative5288 p) (nonnegative5405 p)
def d5416 (p : Pattern) : Int := if p 163 then d5315 p else d5408 p
theorem agree5416 (p q : Pattern) (h : Agree support p q) : d5416 p = d5416 q := by
  simp only [d5416, h 163 (by decide), agree5315 p q h, agree5408 p q h]
theorem nonnegative5416 (p : Pattern) : 0 ≤ d5416 p :=
  nonnegative_ite (p 163) (nonnegative5315 p) (nonnegative5408 p)
def d5417 (p : Pattern) : Int := if p 162 then d5416 p else d5415 p
theorem agree5417 (p q : Pattern) (h : Agree support p q) : d5417 p = d5417 q := by
  simp only [d5417, h 162 (by decide), agree5416 p q h, agree5415 p q h]
theorem nonnegative5417 (p : Pattern) : 0 ≤ d5417 p :=
  nonnegative_ite (p 162) (nonnegative5416 p) (nonnegative5415 p)
def d5418 (p : Pattern) : Int := if p 163 then d12 p else d5408 p
theorem agree5418 (p q : Pattern) (h : Agree support p q) : d5418 p = d5418 q := by
  simp only [d5418, h 163 (by decide), agree12 p q h, agree5408 p q h]
theorem nonnegative5418 (p : Pattern) : 0 ≤ d5418 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5408 p)
def d5419 (p : Pattern) : Int := if p 162 then d12 p else d5418 p
theorem agree5419 (p q : Pattern) (h : Agree support p q) : d5419 p = d5419 q := by
  simp only [d5419, h 162 (by decide), agree12 p q h, agree5418 p q h]
theorem nonnegative5419 (p : Pattern) : 0 ≤ d5419 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5418 p)
def d5420 (p : Pattern) : Int := if p 161 then d5419 p else d5417 p
theorem agree5420 (p q : Pattern) (h : Agree support p q) : d5420 p = d5420 q := by
  simp only [d5420, h 161 (by decide), agree5419 p q h, agree5417 p q h]
theorem nonnegative5420 (p : Pattern) : 0 ≤ d5420 p :=
  nonnegative_ite (p 161) (nonnegative5419 p) (nonnegative5417 p)
def d5421 (p : Pattern) : Int := if p 160 then d5420 p else d5308 p
theorem agree5421 (p q : Pattern) (h : Agree support p q) : d5421 p = d5421 q := by
  simp only [d5421, h 160 (by decide), agree5420 p q h, agree5308 p q h]
theorem nonnegative5421 (p : Pattern) : 0 ≤ d5421 p :=
  nonnegative_ite (p 160) (nonnegative5420 p) (nonnegative5308 p)
def d5422 (p : Pattern) : Int := if p 141 then d5421 p else d5414 p
theorem agree5422 (p q : Pattern) (h : Agree support p q) : d5422 p = d5422 q := by
  simp only [d5422, h 141 (by decide), agree5421 p q h, agree5414 p q h]
theorem nonnegative5422 (p : Pattern) : 0 ≤ d5422 p :=
  nonnegative_ite (p 141) (nonnegative5421 p) (nonnegative5414 p)
def d5423 (p : Pattern) : Int := if p 162 then d5322 p else d5271 p
theorem agree5423 (p q : Pattern) (h : Agree support p q) : d5423 p = d5423 q := by
  simp only [d5423, h 162 (by decide), agree5322 p q h, agree5271 p q h]
theorem nonnegative5423 (p : Pattern) : 0 ≤ d5423 p :=
  nonnegative_ite (p 162) (nonnegative5322 p) (nonnegative5271 p)
def d5424 (p : Pattern) : Int := if p 161 then d5323 p else d5423 p
theorem agree5424 (p q : Pattern) (h : Agree support p q) : d5424 p = d5424 q := by
  simp only [d5424, h 161 (by decide), agree5323 p q h, agree5423 p q h]
theorem nonnegative5424 (p : Pattern) : 0 ≤ d5424 p :=
  nonnegative_ite (p 161) (nonnegative5323 p) (nonnegative5423 p)
def d5425 (p : Pattern) : Int := if p 204 then d12 p else d190 p
theorem agree5425 (p q : Pattern) (h : Agree support p q) : d5425 p = d5425 q := by
  simp only [d5425, h 204 (by decide), agree12 p q h, agree190 p q h]
theorem nonnegative5425 (p : Pattern) : 0 ≤ d5425 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative190 p)
def d5426 (p : Pattern) : Int := if p 182 then d5425 p else d190 p
theorem agree5426 (p q : Pattern) (h : Agree support p q) : d5426 p = d5426 q := by
  simp only [d5426, h 182 (by decide), agree5425 p q h, agree190 p q h]
theorem nonnegative5426 (p : Pattern) : 0 ≤ d5426 p :=
  nonnegative_ite (p 182) (nonnegative5425 p) (nonnegative190 p)
def d5427 (p : Pattern) : Int := if p 163 then d5426 p else d5273 p
theorem agree5427 (p q : Pattern) (h : Agree support p q) : d5427 p = d5427 q := by
  simp only [d5427, h 163 (by decide), agree5426 p q h, agree5273 p q h]
theorem nonnegative5427 (p : Pattern) : 0 ≤ d5427 p :=
  nonnegative_ite (p 163) (nonnegative5426 p) (nonnegative5273 p)
def d5428 (p : Pattern) : Int := if p 162 then d12 p else d5427 p
theorem agree5428 (p q : Pattern) (h : Agree support p q) : d5428 p = d5428 q := by
  simp only [d5428, h 162 (by decide), agree12 p q h, agree5427 p q h]
theorem nonnegative5428 (p : Pattern) : 0 ≤ d5428 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5427 p)
def d5429 (p : Pattern) : Int := if p 161 then d12 p else d5428 p
theorem agree5429 (p q : Pattern) (h : Agree support p q) : d5429 p = d5429 q := by
  simp only [d5429, h 161 (by decide), agree12 p q h, agree5428 p q h]
theorem nonnegative5429 (p : Pattern) : 0 ≤ d5429 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5428 p)
def d5430 (p : Pattern) : Int := if p 160 then d5429 p else d5424 p
theorem agree5430 (p q : Pattern) (h : Agree support p q) : d5430 p = d5430 q := by
  simp only [d5430, h 160 (by decide), agree5429 p q h, agree5424 p q h]
theorem nonnegative5430 (p : Pattern) : 0 ≤ d5430 p :=
  nonnegative_ite (p 160) (nonnegative5429 p) (nonnegative5424 p)
def d5431 (p : Pattern) : Int := if p 163 then d5305 p else d5273 p
theorem agree5431 (p q : Pattern) (h : Agree support p q) : d5431 p = d5431 q := by
  simp only [d5431, h 163 (by decide), agree5305 p q h, agree5273 p q h]
theorem nonnegative5431 (p : Pattern) : 0 ≤ d5431 p :=
  nonnegative_ite (p 163) (nonnegative5305 p) (nonnegative5273 p)
def d5432 (p : Pattern) : Int := if p 162 then d5431 p else d5298 p
theorem agree5432 (p q : Pattern) (h : Agree support p q) : d5432 p = d5432 q := by
  simp only [d5432, h 162 (by decide), agree5431 p q h, agree5298 p q h]
theorem nonnegative5432 (p : Pattern) : 0 ≤ d5432 p :=
  nonnegative_ite (p 162) (nonnegative5431 p) (nonnegative5298 p)
def d5433 (p : Pattern) : Int := if p 161 then d5327 p else d5432 p
theorem agree5433 (p q : Pattern) (h : Agree support p q) : d5433 p = d5433 q := by
  simp only [d5433, h 161 (by decide), agree5327 p q h, agree5432 p q h]
theorem nonnegative5433 (p : Pattern) : 0 ≤ d5433 p :=
  nonnegative_ite (p 161) (nonnegative5327 p) (nonnegative5432 p)
def d5434 (p : Pattern) : Int := if p 163 then d12 p else d5426 p
theorem agree5434 (p q : Pattern) (h : Agree support p q) : d5434 p = d5434 q := by
  simp only [d5434, h 163 (by decide), agree12 p q h, agree5426 p q h]
theorem nonnegative5434 (p : Pattern) : 0 ≤ d5434 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5426 p)
def d5435 (p : Pattern) : Int := if p 162 then d12 p else d5434 p
theorem agree5435 (p q : Pattern) (h : Agree support p q) : d5435 p = d5435 q := by
  simp only [d5435, h 162 (by decide), agree12 p q h, agree5434 p q h]
theorem nonnegative5435 (p : Pattern) : 0 ≤ d5435 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5434 p)
def d5436 (p : Pattern) : Int := if p 161 then d12 p else d5435 p
theorem agree5436 (p q : Pattern) (h : Agree support p q) : d5436 p = d5436 q := by
  simp only [d5436, h 161 (by decide), agree12 p q h, agree5435 p q h]
theorem nonnegative5436 (p : Pattern) : 0 ≤ d5436 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5435 p)
def d5437 (p : Pattern) : Int := if p 160 then d5436 p else d5433 p
theorem agree5437 (p q : Pattern) (h : Agree support p q) : d5437 p = d5437 q := by
  simp only [d5437, h 160 (by decide), agree5436 p q h, agree5433 p q h]
theorem nonnegative5437 (p : Pattern) : 0 ≤ d5437 p :=
  nonnegative_ite (p 160) (nonnegative5436 p) (nonnegative5433 p)
def d5438 (p : Pattern) : Int := if p 141 then d5437 p else d5430 p
theorem agree5438 (p q : Pattern) (h : Agree support p q) : d5438 p = d5438 q := by
  simp only [d5438, h 141 (by decide), agree5437 p q h, agree5430 p q h]
theorem nonnegative5438 (p : Pattern) : 0 ≤ d5438 p :=
  nonnegative_ite (p 141) (nonnegative5437 p) (nonnegative5430 p)
def d5439 (p : Pattern) : Int := if p 138 then d5438 p else d5422 p
theorem agree5439 (p q : Pattern) (h : Agree support p q) : d5439 p = d5439 q := by
  simp only [d5439, h 138 (by decide), agree5438 p q h, agree5422 p q h]
theorem nonnegative5439 (p : Pattern) : 0 ≤ d5439 p :=
  nonnegative_ite (p 138) (nonnegative5438 p) (nonnegative5422 p)
def d5440 (p : Pattern) : Int := if p 138 then d12 p else d5438 p
theorem agree5440 (p q : Pattern) (h : Agree support p q) : d5440 p = d5440 q := by
  simp only [d5440, h 138 (by decide), agree12 p q h, agree5438 p q h]
theorem nonnegative5440 (p : Pattern) : 0 ≤ d5440 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5438 p)
def d5441 (p : Pattern) : Int := if p 116 then d5440 p else d5439 p
theorem agree5441 (p q : Pattern) (h : Agree support p q) : d5441 p = d5441 q := by
  simp only [d5441, h 116 (by decide), agree5440 p q h, agree5439 p q h]
theorem nonnegative5441 (p : Pattern) : 0 ≤ d5441 p :=
  nonnegative_ite (p 116) (nonnegative5440 p) (nonnegative5439 p)
def d5442 (p : Pattern) : Int := if p 115 then d5441 p else d5341 p
theorem agree5442 (p q : Pattern) (h : Agree support p q) : d5442 p = d5442 q := by
  simp only [d5442, h 115 (by decide), agree5441 p q h, agree5341 p q h]
theorem nonnegative5442 (p : Pattern) : 0 ≤ d5442 p :=
  nonnegative_ite (p 115) (nonnegative5441 p) (nonnegative5341 p)
def d5443 (p : Pattern) : Int := if p 71 then d5442 p else d5344 p
theorem agree5443 (p q : Pattern) (h : Agree support p q) : d5443 p = d5443 q := by
  simp only [d5443, h 71 (by decide), agree5442 p q h, agree5344 p q h]
theorem nonnegative5443 (p : Pattern) : 0 ≤ d5443 p :=
  nonnegative_ite (p 71) (nonnegative5442 p) (nonnegative5344 p)
def d5444 (p : Pattern) : Int := if p 163 then d12 p else d5348 p
theorem agree5444 (p q : Pattern) (h : Agree support p q) : d5444 p = d5444 q := by
  simp only [d5444, h 163 (by decide), agree12 p q h, agree5348 p q h]
theorem nonnegative5444 (p : Pattern) : 0 ≤ d5444 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5348 p)
def d5445 (p : Pattern) : Int := if p 162 then d5444 p else d5368 p
theorem agree5445 (p q : Pattern) (h : Agree support p q) : d5445 p = d5445 q := by
  simp only [d5445, h 162 (by decide), agree5444 p q h, agree5368 p q h]
theorem nonnegative5445 (p : Pattern) : 0 ≤ d5445 p :=
  nonnegative_ite (p 162) (nonnegative5444 p) (nonnegative5368 p)
def d5446 (p : Pattern) : Int := if p 162 then d12 p else d5444 p
theorem agree5446 (p q : Pattern) (h : Agree support p q) : d5446 p = d5446 q := by
  simp only [d5446, h 162 (by decide), agree12 p q h, agree5444 p q h]
theorem nonnegative5446 (p : Pattern) : 0 ≤ d5446 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5444 p)
def d5447 (p : Pattern) : Int := if p 161 then d5446 p else d5445 p
theorem agree5447 (p q : Pattern) (h : Agree support p q) : d5447 p = d5447 q := by
  simp only [d5447, h 161 (by decide), agree5446 p q h, agree5445 p q h]
theorem nonnegative5447 (p : Pattern) : 0 ≤ d5447 p :=
  nonnegative_ite (p 161) (nonnegative5446 p) (nonnegative5445 p)
def d5448 (p : Pattern) : Int := if p 163 then d12 p else d5360 p
theorem agree5448 (p q : Pattern) (h : Agree support p q) : d5448 p = d5448 q := by
  simp only [d5448, h 163 (by decide), agree12 p q h, agree5360 p q h]
theorem nonnegative5448 (p : Pattern) : 0 ≤ d5448 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5360 p)
def d5449 (p : Pattern) : Int := if p 162 then d5448 p else d5375 p
theorem agree5449 (p q : Pattern) (h : Agree support p q) : d5449 p = d5449 q := by
  simp only [d5449, h 162 (by decide), agree5448 p q h, agree5375 p q h]
theorem nonnegative5449 (p : Pattern) : 0 ≤ d5449 p :=
  nonnegative_ite (p 162) (nonnegative5448 p) (nonnegative5375 p)
def d5450 (p : Pattern) : Int := if p 162 then d12 p else d5448 p
theorem agree5450 (p q : Pattern) (h : Agree support p q) : d5450 p = d5450 q := by
  simp only [d5450, h 162 (by decide), agree12 p q h, agree5448 p q h]
theorem nonnegative5450 (p : Pattern) : 0 ≤ d5450 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5448 p)
def d5451 (p : Pattern) : Int := if p 161 then d5450 p else d5449 p
theorem agree5451 (p q : Pattern) (h : Agree support p q) : d5451 p = d5451 q := by
  simp only [d5451, h 161 (by decide), agree5450 p q h, agree5449 p q h]
theorem nonnegative5451 (p : Pattern) : 0 ≤ d5451 p :=
  nonnegative_ite (p 161) (nonnegative5450 p) (nonnegative5449 p)
def d5452 (p : Pattern) : Int := if p 160 then d5451 p else d5447 p
theorem agree5452 (p q : Pattern) (h : Agree support p q) : d5452 p = d5452 q := by
  simp only [d5452, h 160 (by decide), agree5451 p q h, agree5447 p q h]
theorem nonnegative5452 (p : Pattern) : 0 ≤ d5452 p :=
  nonnegative_ite (p 160) (nonnegative5451 p) (nonnegative5447 p)
def d5453 (p : Pattern) : Int := if p 141 then d5452 p else d5366 p
theorem agree5453 (p q : Pattern) (h : Agree support p q) : d5453 p = d5453 q := by
  simp only [d5453, h 141 (by decide), agree5452 p q h, agree5366 p q h]
theorem nonnegative5453 (p : Pattern) : 0 ≤ d5453 p :=
  nonnegative_ite (p 141) (nonnegative5452 p) (nonnegative5366 p)
def d5454 (p : Pattern) : Int := if p 160 then d5390 p else d5447 p
theorem agree5454 (p q : Pattern) (h : Agree support p q) : d5454 p = d5454 q := by
  simp only [d5454, h 160 (by decide), agree5390 p q h, agree5447 p q h]
theorem nonnegative5454 (p : Pattern) : 0 ≤ d5454 p :=
  nonnegative_ite (p 160) (nonnegative5390 p) (nonnegative5447 p)
def d5455 (p : Pattern) : Int := if p 141 then d5454 p else d5387 p
theorem agree5455 (p q : Pattern) (h : Agree support p q) : d5455 p = d5455 q := by
  simp only [d5455, h 141 (by decide), agree5454 p q h, agree5387 p q h]
theorem nonnegative5455 (p : Pattern) : 0 ≤ d5455 p :=
  nonnegative_ite (p 141) (nonnegative5454 p) (nonnegative5387 p)
def d5456 (p : Pattern) : Int := if p 138 then d5455 p else d5453 p
theorem agree5456 (p q : Pattern) (h : Agree support p q) : d5456 p = d5456 q := by
  simp only [d5456, h 138 (by decide), agree5455 p q h, agree5453 p q h]
theorem nonnegative5456 (p : Pattern) : 0 ≤ d5456 p :=
  nonnegative_ite (p 138) (nonnegative5455 p) (nonnegative5453 p)
def d5457 (p : Pattern) : Int := if p 138 then d5397 p else d5455 p
theorem agree5457 (p q : Pattern) (h : Agree support p q) : d5457 p = d5457 q := by
  simp only [d5457, h 138 (by decide), agree5397 p q h, agree5455 p q h]
theorem nonnegative5457 (p : Pattern) : 0 ≤ d5457 p :=
  nonnegative_ite (p 138) (nonnegative5397 p) (nonnegative5455 p)
def d5458 (p : Pattern) : Int := if p 116 then d5457 p else d5456 p
theorem agree5458 (p q : Pattern) (h : Agree support p q) : d5458 p = d5458 q := by
  simp only [d5458, h 116 (by decide), agree5457 p q h, agree5456 p q h]
theorem nonnegative5458 (p : Pattern) : 0 ≤ d5458 p :=
  nonnegative_ite (p 116) (nonnegative5457 p) (nonnegative5456 p)
def d5459 (p : Pattern) : Int := if p 182 then d5356 p else d115 p
theorem agree5459 (p q : Pattern) (h : Agree support p q) : d5459 p = d5459 q := by
  simp only [d5459, h 182 (by decide), agree5356 p q h, agree115 p q h]
theorem nonnegative5459 (p : Pattern) : 0 ≤ d5459 p :=
  nonnegative_ite (p 182) (nonnegative5356 p) (nonnegative115 p)
def d5460 (p : Pattern) : Int := if p 163 then d5459 p else d5367 p
theorem agree5460 (p q : Pattern) (h : Agree support p q) : d5460 p = d5460 q := by
  simp only [d5460, h 163 (by decide), agree5459 p q h, agree5367 p q h]
theorem nonnegative5460 (p : Pattern) : 0 ≤ d5460 p :=
  nonnegative_ite (p 163) (nonnegative5459 p) (nonnegative5367 p)
def d5461 (p : Pattern) : Int := if p 162 then d5448 p else d5460 p
theorem agree5461 (p q : Pattern) (h : Agree support p q) : d5461 p = d5461 q := by
  simp only [d5461, h 162 (by decide), agree5448 p q h, agree5460 p q h]
theorem nonnegative5461 (p : Pattern) : 0 ≤ d5461 p :=
  nonnegative_ite (p 162) (nonnegative5448 p) (nonnegative5460 p)
def d5462 (p : Pattern) : Int := if p 182 then d12 p else d119 p
theorem agree5462 (p q : Pattern) (h : Agree support p q) : d5462 p = d5462 q := by
  simp only [d5462, h 182 (by decide), agree12 p q h, agree119 p q h]
theorem nonnegative5462 (p : Pattern) : 0 ≤ d5462 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative119 p)
def d5463 (p : Pattern) : Int := if p 163 then d12 p else d5462 p
theorem agree5463 (p q : Pattern) (h : Agree support p q) : d5463 p = d5463 q := by
  simp only [d5463, h 163 (by decide), agree12 p q h, agree5462 p q h]
theorem nonnegative5463 (p : Pattern) : 0 ≤ d5463 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5462 p)
def d5464 (p : Pattern) : Int := if p 162 then d12 p else d5463 p
theorem agree5464 (p q : Pattern) (h : Agree support p q) : d5464 p = d5464 q := by
  simp only [d5464, h 162 (by decide), agree12 p q h, agree5463 p q h]
theorem nonnegative5464 (p : Pattern) : 0 ≤ d5464 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5463 p)
def d5465 (p : Pattern) : Int := if p 161 then d5464 p else d5461 p
theorem agree5465 (p q : Pattern) (h : Agree support p q) : d5465 p = d5465 q := by
  simp only [d5465, h 161 (by decide), agree5464 p q h, agree5461 p q h]
theorem nonnegative5465 (p : Pattern) : 0 ≤ d5465 p :=
  nonnegative_ite (p 161) (nonnegative5464 p) (nonnegative5461 p)
def d5466 (p : Pattern) : Int := if p 160 then d5465 p else d5353 p
theorem agree5466 (p q : Pattern) (h : Agree support p q) : d5466 p = d5466 q := by
  simp only [d5466, h 160 (by decide), agree5465 p q h, agree5353 p q h]
theorem nonnegative5466 (p : Pattern) : 0 ≤ d5466 p :=
  nonnegative_ite (p 160) (nonnegative5465 p) (nonnegative5353 p)
def d5467 (p : Pattern) : Int := if p 182 then d5356 p else d106 p
theorem agree5467 (p q : Pattern) (h : Agree support p q) : d5467 p = d5467 q := by
  simp only [d5467, h 182 (by decide), agree5356 p q h, agree106 p q h]
theorem nonnegative5467 (p : Pattern) : 0 ≤ d5467 p :=
  nonnegative_ite (p 182) (nonnegative5356 p) (nonnegative106 p)
def d5468 (p : Pattern) : Int := if p 163 then d5360 p else d5467 p
theorem agree5468 (p q : Pattern) (h : Agree support p q) : d5468 p = d5468 q := by
  simp only [d5468, h 163 (by decide), agree5360 p q h, agree5467 p q h]
theorem nonnegative5468 (p : Pattern) : 0 ≤ d5468 p :=
  nonnegative_ite (p 163) (nonnegative5360 p) (nonnegative5467 p)
def d5469 (p : Pattern) : Int := if p 162 then d5463 p else d5468 p
theorem agree5469 (p q : Pattern) (h : Agree support p q) : d5469 p = d5469 q := by
  simp only [d5469, h 162 (by decide), agree5463 p q h, agree5468 p q h]
theorem nonnegative5469 (p : Pattern) : 0 ≤ d5469 p :=
  nonnegative_ite (p 162) (nonnegative5463 p) (nonnegative5468 p)
def d5470 (p : Pattern) : Int := if p 162 then d12 p else d5294 p
theorem agree5470 (p q : Pattern) (h : Agree support p q) : d5470 p = d5470 q := by
  simp only [d5470, h 162 (by decide), agree12 p q h, agree5294 p q h]
theorem nonnegative5470 (p : Pattern) : 0 ≤ d5470 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5294 p)
def d5471 (p : Pattern) : Int := if p 161 then d5470 p else d5469 p
theorem agree5471 (p q : Pattern) (h : Agree support p q) : d5471 p = d5471 q := by
  simp only [d5471, h 161 (by decide), agree5470 p q h, agree5469 p q h]
theorem nonnegative5471 (p : Pattern) : 0 ≤ d5471 p :=
  nonnegative_ite (p 161) (nonnegative5470 p) (nonnegative5469 p)
def d5472 (p : Pattern) : Int := if p 160 then d5471 p else d5447 p
theorem agree5472 (p q : Pattern) (h : Agree support p q) : d5472 p = d5472 q := by
  simp only [d5472, h 160 (by decide), agree5471 p q h, agree5447 p q h]
theorem nonnegative5472 (p : Pattern) : 0 ≤ d5472 p :=
  nonnegative_ite (p 160) (nonnegative5471 p) (nonnegative5447 p)
def d5473 (p : Pattern) : Int := if p 141 then d5472 p else d5466 p
theorem agree5473 (p q : Pattern) (h : Agree support p q) : d5473 p = d5473 q := by
  simp only [d5473, h 141 (by decide), agree5472 p q h, agree5466 p q h]
theorem nonnegative5473 (p : Pattern) : 0 ≤ d5473 p :=
  nonnegative_ite (p 141) (nonnegative5472 p) (nonnegative5466 p)
def d5474 (p : Pattern) : Int := if p 163 then d5305 p else d5367 p
theorem agree5474 (p q : Pattern) (h : Agree support p q) : d5474 p = d5474 q := by
  simp only [d5474, h 163 (by decide), agree5305 p q h, agree5367 p q h]
theorem nonnegative5474 (p : Pattern) : 0 ≤ d5474 p :=
  nonnegative_ite (p 163) (nonnegative5305 p) (nonnegative5367 p)
def d5475 (p : Pattern) : Int := if p 162 then d5474 p else d5346 p
theorem agree5475 (p q : Pattern) (h : Agree support p q) : d5475 p = d5475 q := by
  simp only [d5475, h 162 (by decide), agree5474 p q h, agree5346 p q h]
theorem nonnegative5475 (p : Pattern) : 0 ≤ d5475 p :=
  nonnegative_ite (p 162) (nonnegative5474 p) (nonnegative5346 p)
def d5476 (p : Pattern) : Int := if p 161 then d5372 p else d5475 p
theorem agree5476 (p q : Pattern) (h : Agree support p q) : d5476 p = d5476 q := by
  simp only [d5476, h 161 (by decide), agree5372 p q h, agree5475 p q h]
theorem nonnegative5476 (p : Pattern) : 0 ≤ d5476 p :=
  nonnegative_ite (p 161) (nonnegative5372 p) (nonnegative5475 p)
def d5477 (p : Pattern) : Int := if p 160 then d5390 p else d5476 p
theorem agree5477 (p q : Pattern) (h : Agree support p q) : d5477 p = d5477 q := by
  simp only [d5477, h 160 (by decide), agree5390 p q h, agree5476 p q h]
theorem nonnegative5477 (p : Pattern) : 0 ≤ d5477 p :=
  nonnegative_ite (p 160) (nonnegative5390 p) (nonnegative5476 p)
def d5478 (p : Pattern) : Int := if p 162 then d5444 p else d5367 p
theorem agree5478 (p q : Pattern) (h : Agree support p q) : d5478 p = d5478 q := by
  simp only [d5478, h 162 (by decide), agree5444 p q h, agree5367 p q h]
theorem nonnegative5478 (p : Pattern) : 0 ≤ d5478 p :=
  nonnegative_ite (p 162) (nonnegative5444 p) (nonnegative5367 p)
def d5479 (p : Pattern) : Int := if p 161 then d5389 p else d5478 p
theorem agree5479 (p q : Pattern) (h : Agree support p q) : d5479 p = d5479 q := by
  simp only [d5479, h 161 (by decide), agree5389 p q h, agree5478 p q h]
theorem nonnegative5479 (p : Pattern) : 0 ≤ d5479 p :=
  nonnegative_ite (p 161) (nonnegative5389 p) (nonnegative5478 p)
def d5480 (p : Pattern) : Int := if p 162 then d12 p else d5278 p
theorem agree5480 (p q : Pattern) (h : Agree support p q) : d5480 p = d5480 q := by
  simp only [d5480, h 162 (by decide), agree12 p q h, agree5278 p q h]
theorem nonnegative5480 (p : Pattern) : 0 ≤ d5480 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5278 p)
def d5481 (p : Pattern) : Int := if p 161 then d12 p else d5480 p
theorem agree5481 (p q : Pattern) (h : Agree support p q) : d5481 p = d5481 q := by
  simp only [d5481, h 161 (by decide), agree12 p q h, agree5480 p q h]
theorem nonnegative5481 (p : Pattern) : 0 ≤ d5481 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5480 p)
def d5482 (p : Pattern) : Int := if p 160 then d5481 p else d5479 p
theorem agree5482 (p q : Pattern) (h : Agree support p q) : d5482 p = d5482 q := by
  simp only [d5482, h 160 (by decide), agree5481 p q h, agree5479 p q h]
theorem nonnegative5482 (p : Pattern) : 0 ≤ d5482 p :=
  nonnegative_ite (p 160) (nonnegative5481 p) (nonnegative5479 p)
def d5483 (p : Pattern) : Int := if p 141 then d5482 p else d5477 p
theorem agree5483 (p q : Pattern) (h : Agree support p q) : d5483 p = d5483 q := by
  simp only [d5483, h 141 (by decide), agree5482 p q h, agree5477 p q h]
theorem nonnegative5483 (p : Pattern) : 0 ≤ d5483 p :=
  nonnegative_ite (p 141) (nonnegative5482 p) (nonnegative5477 p)
def d5484 (p : Pattern) : Int := if p 138 then d5483 p else d5473 p
theorem agree5484 (p q : Pattern) (h : Agree support p q) : d5484 p = d5484 q := by
  simp only [d5484, h 138 (by decide), agree5483 p q h, agree5473 p q h]
theorem nonnegative5484 (p : Pattern) : 0 ≤ d5484 p :=
  nonnegative_ite (p 138) (nonnegative5483 p) (nonnegative5473 p)
def d5485 (p : Pattern) : Int := if p 163 then d5277 p else d5367 p
theorem agree5485 (p q : Pattern) (h : Agree support p q) : d5485 p = d5485 q := by
  simp only [d5485, h 163 (by decide), agree5277 p q h, agree5367 p q h]
theorem nonnegative5485 (p : Pattern) : 0 ≤ d5485 p :=
  nonnegative_ite (p 163) (nonnegative5277 p) (nonnegative5367 p)
def d5486 (p : Pattern) : Int := if p 162 then d5485 p else d5346 p
theorem agree5486 (p q : Pattern) (h : Agree support p q) : d5486 p = d5486 q := by
  simp only [d5486, h 162 (by decide), agree5485 p q h, agree5346 p q h]
theorem nonnegative5486 (p : Pattern) : 0 ≤ d5486 p :=
  nonnegative_ite (p 162) (nonnegative5485 p) (nonnegative5346 p)
def d5487 (p : Pattern) : Int := if p 163 then d5277 p else d5348 p
theorem agree5487 (p q : Pattern) (h : Agree support p q) : d5487 p = d5487 q := by
  simp only [d5487, h 163 (by decide), agree5277 p q h, agree5348 p q h]
theorem nonnegative5487 (p : Pattern) : 0 ≤ d5487 p :=
  nonnegative_ite (p 163) (nonnegative5277 p) (nonnegative5348 p)
def d5488 (p : Pattern) : Int := if p 162 then d12 p else d5487 p
theorem agree5488 (p q : Pattern) (h : Agree support p q) : d5488 p = d5488 q := by
  simp only [d5488, h 162 (by decide), agree12 p q h, agree5487 p q h]
theorem nonnegative5488 (p : Pattern) : 0 ≤ d5488 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5487 p)
def d5489 (p : Pattern) : Int := if p 161 then d5488 p else d5486 p
theorem agree5489 (p q : Pattern) (h : Agree support p q) : d5489 p = d5489 q := by
  simp only [d5489, h 161 (by decide), agree5488 p q h, agree5486 p q h]
theorem nonnegative5489 (p : Pattern) : 0 ≤ d5489 p :=
  nonnegative_ite (p 161) (nonnegative5488 p) (nonnegative5486 p)
def d5490 (p : Pattern) : Int := if p 163 then d5305 p else d5383 p
theorem agree5490 (p q : Pattern) (h : Agree support p q) : d5490 p = d5490 q := by
  simp only [d5490, h 163 (by decide), agree5305 p q h, agree5383 p q h]
theorem nonnegative5490 (p : Pattern) : 0 ≤ d5490 p :=
  nonnegative_ite (p 163) (nonnegative5305 p) (nonnegative5383 p)
def d5491 (p : Pattern) : Int := if p 162 then d12 p else d5490 p
theorem agree5491 (p q : Pattern) (h : Agree support p q) : d5491 p = d5491 q := by
  simp only [d5491, h 162 (by decide), agree12 p q h, agree5490 p q h]
theorem nonnegative5491 (p : Pattern) : 0 ≤ d5491 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5490 p)
def d5492 (p : Pattern) : Int := if p 161 then d12 p else d5491 p
theorem agree5492 (p q : Pattern) (h : Agree support p q) : d5492 p = d5492 q := by
  simp only [d5492, h 161 (by decide), agree12 p q h, agree5491 p q h]
theorem nonnegative5492 (p : Pattern) : 0 ≤ d5492 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5491 p)
def d5493 (p : Pattern) : Int := if p 160 then d5492 p else d5489 p
theorem agree5493 (p q : Pattern) (h : Agree support p q) : d5493 p = d5493 q := by
  simp only [d5493, h 160 (by decide), agree5492 p q h, agree5489 p q h]
theorem nonnegative5493 (p : Pattern) : 0 ≤ d5493 p :=
  nonnegative_ite (p 160) (nonnegative5492 p) (nonnegative5489 p)
def d5494 (p : Pattern) : Int := if p 141 then d5482 p else d5493 p
theorem agree5494 (p q : Pattern) (h : Agree support p q) : d5494 p = d5494 q := by
  simp only [d5494, h 141 (by decide), agree5482 p q h, agree5493 p q h]
theorem nonnegative5494 (p : Pattern) : 0 ≤ d5494 p :=
  nonnegative_ite (p 141) (nonnegative5482 p) (nonnegative5493 p)
def d5495 (p : Pattern) : Int := if p 138 then d12 p else d5494 p
theorem agree5495 (p q : Pattern) (h : Agree support p q) : d5495 p = d5495 q := by
  simp only [d5495, h 138 (by decide), agree12 p q h, agree5494 p q h]
theorem nonnegative5495 (p : Pattern) : 0 ≤ d5495 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5494 p)
def d5496 (p : Pattern) : Int := if p 116 then d5495 p else d5484 p
theorem agree5496 (p q : Pattern) (h : Agree support p q) : d5496 p = d5496 q := by
  simp only [d5496, h 116 (by decide), agree5495 p q h, agree5484 p q h]
theorem nonnegative5496 (p : Pattern) : 0 ≤ d5496 p :=
  nonnegative_ite (p 116) (nonnegative5495 p) (nonnegative5484 p)
def d5497 (p : Pattern) : Int := if p 115 then d5496 p else d5458 p
theorem agree5497 (p q : Pattern) (h : Agree support p q) : d5497 p = d5497 q := by
  simp only [d5497, h 115 (by decide), agree5496 p q h, agree5458 p q h]
theorem nonnegative5497 (p : Pattern) : 0 ≤ d5497 p :=
  nonnegative_ite (p 115) (nonnegative5496 p) (nonnegative5458 p)
def d5498 (p : Pattern) : Int := if p 71 then d5497 p else d5344 p
theorem agree5498 (p q : Pattern) (h : Agree support p q) : d5498 p = d5498 q := by
  simp only [d5498, h 71 (by decide), agree5497 p q h, agree5344 p q h]
theorem nonnegative5498 (p : Pattern) : 0 ≤ d5498 p :=
  nonnegative_ite (p 71) (nonnegative5497 p) (nonnegative5344 p)
def d5499 (p : Pattern) : Int := if p 49 then d5498 p else d5443 p
theorem agree5499 (p q : Pattern) (h : Agree support p q) : d5499 p = d5499 q := by
  simp only [d5499, h 49 (by decide), agree5498 p q h, agree5443 p q h]
theorem nonnegative5499 (p : Pattern) : 0 ≤ d5499 p :=
  nonnegative_ite (p 49) (nonnegative5498 p) (nonnegative5443 p)
def d5500 (p : Pattern) : Int := if p 48 then d5499 p else d5404 p
theorem agree5500 (p q : Pattern) (h : Agree support p q) : d5500 p = d5500 q := by
  simp only [d5500, h 48 (by decide), agree5499 p q h, agree5404 p q h]
theorem nonnegative5500 (p : Pattern) : 0 ≤ d5500 p :=
  nonnegative_ite (p 48) (nonnegative5499 p) (nonnegative5404 p)
def d5501 (p : Pattern) : Int := if p 225 then d1 p else d0 p
theorem agree5501 (p q : Pattern) (h : Agree support p q) : d5501 p = d5501 q := by
  simp only [d5501, h 225 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative5501 (p : Pattern) : 0 ≤ d5501 p :=
  nonnegative_ite (p 225) (nonnegative1 p) (nonnegative0 p)
def d5502 (p : Pattern) : Int := if p 225 then d0 p else d1 p
theorem agree5502 (p q : Pattern) (h : Agree support p q) : d5502 p = d5502 q := by
  simp only [d5502, h 225 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative5502 (p : Pattern) : 0 ≤ d5502 p :=
  nonnegative_ite (p 225) (nonnegative0 p) (nonnegative1 p)
def d5503 (p : Pattern) : Int := if p 224 then d0 p else d5502 p
theorem agree5503 (p q : Pattern) (h : Agree support p q) : d5503 p = d5503 q := by
  simp only [d5503, h 224 (by decide), agree0 p q h, agree5502 p q h]
theorem nonnegative5503 (p : Pattern) : 0 ≤ d5503 p :=
  nonnegative_ite (p 224) (nonnegative0 p) (nonnegative5502 p)
def d5504 (p : Pattern) : Int := if p 141 then d4496 p else d4492 p
theorem agree5504 (p q : Pattern) (h : Agree support p q) : d5504 p = d5504 q := by
  simp only [d5504, h 141 (by decide), agree4496 p q h, agree4492 p q h]
theorem nonnegative5504 (p : Pattern) : 0 ≤ d5504 p :=
  nonnegative_ite (p 141) (nonnegative4496 p) (nonnegative4492 p)
def d5505 (p : Pattern) : Int := if p 138 then d5504 p else d4489 p
theorem agree5505 (p q : Pattern) (h : Agree support p q) : d5505 p = d5505 q := by
  simp only [d5505, h 138 (by decide), agree5504 p q h, agree4489 p q h]
theorem nonnegative5505 (p : Pattern) : 0 ≤ d5505 p :=
  nonnegative_ite (p 138) (nonnegative5504 p) (nonnegative4489 p)
def d5506 (p : Pattern) : Int := if p 141 then d12 p else d4504 p
theorem agree5506 (p q : Pattern) (h : Agree support p q) : d5506 p = d5506 q := by
  simp only [d5506, h 141 (by decide), agree12 p q h, agree4504 p q h]
theorem nonnegative5506 (p : Pattern) : 0 ≤ d5506 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative4504 p)
def d5507 (p : Pattern) : Int := if p 138 then d5506 p else d5504 p
theorem agree5507 (p q : Pattern) (h : Agree support p q) : d5507 p = d5507 q := by
  simp only [d5507, h 138 (by decide), agree5506 p q h, agree5504 p q h]
theorem nonnegative5507 (p : Pattern) : 0 ≤ d5507 p :=
  nonnegative_ite (p 138) (nonnegative5506 p) (nonnegative5504 p)
def d5508 (p : Pattern) : Int := if p 116 then d5507 p else d5505 p
theorem agree5508 (p q : Pattern) (h : Agree support p q) : d5508 p = d5508 q := by
  simp only [d5508, h 116 (by decide), agree5507 p q h, agree5505 p q h]
theorem nonnegative5508 (p : Pattern) : 0 ≤ d5508 p :=
  nonnegative_ite (p 116) (nonnegative5507 p) (nonnegative5505 p)
def d5509 (p : Pattern) : Int := if p 138 then d12 p else d5504 p
theorem agree5509 (p q : Pattern) (h : Agree support p q) : d5509 p = d5509 q := by
  simp only [d5509, h 138 (by decide), agree12 p q h, agree5504 p q h]
theorem nonnegative5509 (p : Pattern) : 0 ≤ d5509 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5504 p)
def d5510 (p : Pattern) : Int := if p 116 then d5509 p else d5505 p
theorem agree5510 (p q : Pattern) (h : Agree support p q) : d5510 p = d5510 q := by
  simp only [d5510, h 116 (by decide), agree5509 p q h, agree5505 p q h]
theorem nonnegative5510 (p : Pattern) : 0 ≤ d5510 p :=
  nonnegative_ite (p 116) (nonnegative5509 p) (nonnegative5505 p)
def d5511 (p : Pattern) : Int := if p 115 then d5510 p else d5508 p
theorem agree5511 (p q : Pattern) (h : Agree support p q) : d5511 p = d5511 q := by
  simp only [d5511, h 115 (by decide), agree5510 p q h, agree5508 p q h]
theorem nonnegative5511 (p : Pattern) : 0 ≤ d5511 p :=
  nonnegative_ite (p 115) (nonnegative5510 p) (nonnegative5508 p)
def d5512 (p : Pattern) : Int := if p 141 then d4531 p else d4527 p
theorem agree5512 (p q : Pattern) (h : Agree support p q) : d5512 p = d5512 q := by
  simp only [d5512, h 141 (by decide), agree4531 p q h, agree4527 p q h]
theorem nonnegative5512 (p : Pattern) : 0 ≤ d5512 p :=
  nonnegative_ite (p 141) (nonnegative4531 p) (nonnegative4527 p)
def d5513 (p : Pattern) : Int := if p 138 then d5512 p else d4524 p
theorem agree5513 (p q : Pattern) (h : Agree support p q) : d5513 p = d5513 q := by
  simp only [d5513, h 138 (by decide), agree5512 p q h, agree4524 p q h]
theorem nonnegative5513 (p : Pattern) : 0 ≤ d5513 p :=
  nonnegative_ite (p 138) (nonnegative5512 p) (nonnegative4524 p)
def d5514 (p : Pattern) : Int := if p 138 then d12 p else d5512 p
theorem agree5514 (p q : Pattern) (h : Agree support p q) : d5514 p = d5514 q := by
  simp only [d5514, h 138 (by decide), agree12 p q h, agree5512 p q h]
theorem nonnegative5514 (p : Pattern) : 0 ≤ d5514 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5512 p)
def d5515 (p : Pattern) : Int := if p 116 then d5514 p else d5513 p
theorem agree5515 (p q : Pattern) (h : Agree support p q) : d5515 p = d5515 q := by
  simp only [d5515, h 116 (by decide), agree5514 p q h, agree5513 p q h]
theorem nonnegative5515 (p : Pattern) : 0 ≤ d5515 p :=
  nonnegative_ite (p 116) (nonnegative5514 p) (nonnegative5513 p)
def d5516 (p : Pattern) : Int := if p 71 then d5515 p else d5511 p
theorem agree5516 (p q : Pattern) (h : Agree support p q) : d5516 p = d5516 q := by
  simp only [d5516, h 71 (by decide), agree5515 p q h, agree5511 p q h]
theorem nonnegative5516 (p : Pattern) : 0 ≤ d5516 p :=
  nonnegative_ite (p 71) (nonnegative5515 p) (nonnegative5511 p)
def d5517 (p : Pattern) : Int := if p 49 then d5516 p else d5511 p
theorem agree5517 (p q : Pattern) (h : Agree support p q) : d5517 p = d5517 q := by
  simp only [d5517, h 49 (by decide), agree5516 p q h, agree5511 p q h]
theorem nonnegative5517 (p : Pattern) : 0 ≤ d5517 p :=
  nonnegative_ite (p 49) (nonnegative5516 p) (nonnegative5511 p)
def d5518 (p : Pattern) : Int := if p 141 then d4552 p else d4547 p
theorem agree5518 (p q : Pattern) (h : Agree support p q) : d5518 p = d5518 q := by
  simp only [d5518, h 141 (by decide), agree4552 p q h, agree4547 p q h]
theorem nonnegative5518 (p : Pattern) : 0 ≤ d5518 p :=
  nonnegative_ite (p 141) (nonnegative4552 p) (nonnegative4547 p)
def d5519 (p : Pattern) : Int := if p 141 then d4566 p else d4559 p
theorem agree5519 (p q : Pattern) (h : Agree support p q) : d5519 p = d5519 q := by
  simp only [d5519, h 141 (by decide), agree4566 p q h, agree4559 p q h]
theorem nonnegative5519 (p : Pattern) : 0 ≤ d5519 p :=
  nonnegative_ite (p 141) (nonnegative4566 p) (nonnegative4559 p)
end NetHack.Sokoban22Refined85
