/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes43
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d5280 (p : Pattern) : Int := if p 161 then d5279 p else d5275 p
theorem agree5280 (p q : Pattern) (h : Agree support p q) : d5280 p = d5280 q := by
  simp only [d5280, h 161 (by decide), agree5279 p q h, agree5275 p q h]
theorem nonnegative5280 (p : Pattern) : 0 ≤ d5280 p :=
  nonnegative_ite (p 161) (nonnegative5279 p) (nonnegative5275 p)
def d5281 (p : Pattern) : Int := if p 204 then d12 p else d30 p
theorem agree5281 (p q : Pattern) (h : Agree support p q) : d5281 p = d5281 q := by
  simp only [d5281, h 204 (by decide), agree12 p q h, agree30 p q h]
theorem nonnegative5281 (p : Pattern) : 0 ≤ d5281 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative30 p)
def d5282 (p : Pattern) : Int := if p 182 then d5281 p else d13 p
theorem agree5282 (p q : Pattern) (h : Agree support p q) : d5282 p = d5282 q := by
  simp only [d5282, h 182 (by decide), agree5281 p q h, agree13 p q h]
theorem nonnegative5282 (p : Pattern) : 0 ≤ d5282 p :=
  nonnegative_ite (p 182) (nonnegative5281 p) (nonnegative13 p)
def d5283 (p : Pattern) : Int := if p 204 then d12 p else d34 p
theorem agree5283 (p q : Pattern) (h : Agree support p q) : d5283 p = d5283 q := by
  simp only [d5283, h 204 (by decide), agree12 p q h, agree34 p q h]
theorem nonnegative5283 (p : Pattern) : 0 ≤ d5283 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative34 p)
def d5284 (p : Pattern) : Int := if p 182 then d5283 p else d13 p
theorem agree5284 (p q : Pattern) (h : Agree support p q) : d5284 p = d5284 q := by
  simp only [d5284, h 182 (by decide), agree5283 p q h, agree13 p q h]
theorem nonnegative5284 (p : Pattern) : 0 ≤ d5284 p :=
  nonnegative_ite (p 182) (nonnegative5283 p) (nonnegative13 p)
def d5285 (p : Pattern) : Int := if p 163 then d5284 p else d5282 p
theorem agree5285 (p q : Pattern) (h : Agree support p q) : d5285 p = d5285 q := by
  simp only [d5285, h 163 (by decide), agree5284 p q h, agree5282 p q h]
theorem nonnegative5285 (p : Pattern) : 0 ≤ d5285 p :=
  nonnegative_ite (p 163) (nonnegative5284 p) (nonnegative5282 p)
def d5286 (p : Pattern) : Int := if p 204 then d12 p else d39 p
theorem agree5286 (p q : Pattern) (h : Agree support p q) : d5286 p = d5286 q := by
  simp only [d5286, h 204 (by decide), agree12 p q h, agree39 p q h]
theorem nonnegative5286 (p : Pattern) : 0 ≤ d5286 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative39 p)
def d5287 (p : Pattern) : Int := if p 182 then d5286 p else d13 p
theorem agree5287 (p q : Pattern) (h : Agree support p q) : d5287 p = d5287 q := by
  simp only [d5287, h 182 (by decide), agree5286 p q h, agree13 p q h]
theorem nonnegative5287 (p : Pattern) : 0 ≤ d5287 p :=
  nonnegative_ite (p 182) (nonnegative5286 p) (nonnegative13 p)
def d5288 (p : Pattern) : Int := if p 182 then d12 p else d17 p
theorem agree5288 (p q : Pattern) (h : Agree support p q) : d5288 p = d5288 q := by
  simp only [d5288, h 182 (by decide), agree12 p q h, agree17 p q h]
theorem nonnegative5288 (p : Pattern) : 0 ≤ d5288 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative17 p)
def d5289 (p : Pattern) : Int := if p 163 then d5288 p else d5287 p
theorem agree5289 (p q : Pattern) (h : Agree support p q) : d5289 p = d5289 q := by
  simp only [d5289, h 163 (by decide), agree5288 p q h, agree5287 p q h]
theorem nonnegative5289 (p : Pattern) : 0 ≤ d5289 p :=
  nonnegative_ite (p 163) (nonnegative5288 p) (nonnegative5287 p)
def d5290 (p : Pattern) : Int := if p 162 then d5289 p else d5285 p
theorem agree5290 (p q : Pattern) (h : Agree support p q) : d5290 p = d5290 q := by
  simp only [d5290, h 162 (by decide), agree5289 p q h, agree5285 p q h]
theorem nonnegative5290 (p : Pattern) : 0 ≤ d5290 p :=
  nonnegative_ite (p 162) (nonnegative5289 p) (nonnegative5285 p)
def d5291 (p : Pattern) : Int := if p 182 then d12 p else d13 p
theorem agree5291 (p q : Pattern) (h : Agree support p q) : d5291 p = d5291 q := by
  simp only [d5291, h 182 (by decide), agree12 p q h, agree13 p q h]
theorem nonnegative5291 (p : Pattern) : 0 ≤ d5291 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative13 p)
def d5292 (p : Pattern) : Int := if p 163 then d5288 p else d5291 p
theorem agree5292 (p q : Pattern) (h : Agree support p q) : d5292 p = d5292 q := by
  simp only [d5292, h 163 (by decide), agree5288 p q h, agree5291 p q h]
theorem nonnegative5292 (p : Pattern) : 0 ≤ d5292 p :=
  nonnegative_ite (p 163) (nonnegative5288 p) (nonnegative5291 p)
def d5293 (p : Pattern) : Int := if p 182 then d12 p else d23 p
theorem agree5293 (p q : Pattern) (h : Agree support p q) : d5293 p = d5293 q := by
  simp only [d5293, h 182 (by decide), agree12 p q h, agree23 p q h]
theorem nonnegative5293 (p : Pattern) : 0 ≤ d5293 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative23 p)
def d5294 (p : Pattern) : Int := if p 163 then d12 p else d5293 p
theorem agree5294 (p q : Pattern) (h : Agree support p q) : d5294 p = d5294 q := by
  simp only [d5294, h 163 (by decide), agree12 p q h, agree5293 p q h]
theorem nonnegative5294 (p : Pattern) : 0 ≤ d5294 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5293 p)
def d5295 (p : Pattern) : Int := if p 162 then d5294 p else d5292 p
theorem agree5295 (p q : Pattern) (h : Agree support p q) : d5295 p = d5295 q := by
  simp only [d5295, h 162 (by decide), agree5294 p q h, agree5292 p q h]
theorem nonnegative5295 (p : Pattern) : 0 ≤ d5295 p :=
  nonnegative_ite (p 162) (nonnegative5294 p) (nonnegative5292 p)
def d5296 (p : Pattern) : Int := if p 161 then d5295 p else d5290 p
theorem agree5296 (p q : Pattern) (h : Agree support p q) : d5296 p = d5296 q := by
  simp only [d5296, h 161 (by decide), agree5295 p q h, agree5290 p q h]
theorem nonnegative5296 (p : Pattern) : 0 ≤ d5296 p :=
  nonnegative_ite (p 161) (nonnegative5295 p) (nonnegative5290 p)
def d5297 (p : Pattern) : Int := if p 160 then d5296 p else d5280 p
theorem agree5297 (p q : Pattern) (h : Agree support p q) : d5297 p = d5297 q := by
  simp only [d5297, h 160 (by decide), agree5296 p q h, agree5280 p q h]
theorem nonnegative5297 (p : Pattern) : 0 ≤ d5297 p :=
  nonnegative_ite (p 160) (nonnegative5296 p) (nonnegative5280 p)
def d5298 (p : Pattern) : Int := if p 182 then d5281 p else d30 p
theorem agree5298 (p q : Pattern) (h : Agree support p q) : d5298 p = d5298 q := by
  simp only [d5298, h 182 (by decide), agree5281 p q h, agree30 p q h]
theorem nonnegative5298 (p : Pattern) : 0 ≤ d5298 p :=
  nonnegative_ite (p 182) (nonnegative5281 p) (nonnegative30 p)
def d5299 (p : Pattern) : Int := if p 163 then d5298 p else d5271 p
theorem agree5299 (p q : Pattern) (h : Agree support p q) : d5299 p = d5299 q := by
  simp only [d5299, h 163 (by decide), agree5298 p q h, agree5271 p q h]
theorem nonnegative5299 (p : Pattern) : 0 ≤ d5299 p :=
  nonnegative_ite (p 163) (nonnegative5298 p) (nonnegative5271 p)
def d5300 (p : Pattern) : Int := if p 163 then d5277 p else d5273 p
theorem agree5300 (p q : Pattern) (h : Agree support p q) : d5300 p = d5300 q := by
  simp only [d5300, h 163 (by decide), agree5277 p q h, agree5273 p q h]
theorem nonnegative5300 (p : Pattern) : 0 ≤ d5300 p :=
  nonnegative_ite (p 163) (nonnegative5277 p) (nonnegative5273 p)
def d5301 (p : Pattern) : Int := if p 162 then d5300 p else d5299 p
theorem agree5301 (p q : Pattern) (h : Agree support p q) : d5301 p = d5301 q := by
  simp only [d5301, h 162 (by decide), agree5300 p q h, agree5299 p q h]
theorem nonnegative5301 (p : Pattern) : 0 ≤ d5301 p :=
  nonnegative_ite (p 162) (nonnegative5300 p) (nonnegative5299 p)
def d5302 (p : Pattern) : Int := if p 204 then d12 p else d57 p
theorem agree5302 (p q : Pattern) (h : Agree support p q) : d5302 p = d5302 q := by
  simp only [d5302, h 204 (by decide), agree12 p q h, agree57 p q h]
theorem nonnegative5302 (p : Pattern) : 0 ≤ d5302 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative57 p)
def d5303 (p : Pattern) : Int := if p 182 then d5302 p else d57 p
theorem agree5303 (p q : Pattern) (h : Agree support p q) : d5303 p = d5303 q := by
  simp only [d5303, h 182 (by decide), agree5302 p q h, agree57 p q h]
theorem nonnegative5303 (p : Pattern) : 0 ≤ d5303 p :=
  nonnegative_ite (p 182) (nonnegative5302 p) (nonnegative57 p)
def d5304 (p : Pattern) : Int := if p 163 then d5303 p else d5273 p
theorem agree5304 (p q : Pattern) (h : Agree support p q) : d5304 p = d5304 q := by
  simp only [d5304, h 163 (by decide), agree5303 p q h, agree5273 p q h]
theorem nonnegative5304 (p : Pattern) : 0 ≤ d5304 p :=
  nonnegative_ite (p 163) (nonnegative5303 p) (nonnegative5273 p)
def d5305 (p : Pattern) : Int := if p 182 then d5286 p else d39 p
theorem agree5305 (p q : Pattern) (h : Agree support p q) : d5305 p = d5305 q := by
  simp only [d5305, h 182 (by decide), agree5286 p q h, agree39 p q h]
theorem nonnegative5305 (p : Pattern) : 0 ≤ d5305 p :=
  nonnegative_ite (p 182) (nonnegative5286 p) (nonnegative39 p)
def d5306 (p : Pattern) : Int := if p 163 then d12 p else d5305 p
theorem agree5306 (p q : Pattern) (h : Agree support p q) : d5306 p = d5306 q := by
  simp only [d5306, h 163 (by decide), agree12 p q h, agree5305 p q h]
theorem nonnegative5306 (p : Pattern) : 0 ≤ d5306 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5305 p)
def d5307 (p : Pattern) : Int := if p 162 then d5306 p else d5304 p
theorem agree5307 (p q : Pattern) (h : Agree support p q) : d5307 p = d5307 q := by
  simp only [d5307, h 162 (by decide), agree5306 p q h, agree5304 p q h]
theorem nonnegative5307 (p : Pattern) : 0 ≤ d5307 p :=
  nonnegative_ite (p 162) (nonnegative5306 p) (nonnegative5304 p)
def d5308 (p : Pattern) : Int := if p 161 then d5307 p else d5301 p
theorem agree5308 (p q : Pattern) (h : Agree support p q) : d5308 p = d5308 q := by
  simp only [d5308, h 161 (by decide), agree5307 p q h, agree5301 p q h]
theorem nonnegative5308 (p : Pattern) : 0 ≤ d5308 p :=
  nonnegative_ite (p 161) (nonnegative5307 p) (nonnegative5301 p)
def d5309 (p : Pattern) : Int := if p 182 then d12 p else d30 p
theorem agree5309 (p q : Pattern) (h : Agree support p q) : d5309 p = d5309 q := by
  simp only [d5309, h 182 (by decide), agree12 p q h, agree30 p q h]
theorem nonnegative5309 (p : Pattern) : 0 ≤ d5309 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative30 p)
def d5310 (p : Pattern) : Int := if p 163 then d5309 p else d5284 p
theorem agree5310 (p q : Pattern) (h : Agree support p q) : d5310 p = d5310 q := by
  simp only [d5310, h 163 (by decide), agree5309 p q h, agree5284 p q h]
theorem nonnegative5310 (p : Pattern) : 0 ≤ d5310 p :=
  nonnegative_ite (p 163) (nonnegative5309 p) (nonnegative5284 p)
def d5311 (p : Pattern) : Int := if p 163 then d5293 p else d5288 p
theorem agree5311 (p q : Pattern) (h : Agree support p q) : d5311 p = d5311 q := by
  simp only [d5311, h 163 (by decide), agree5293 p q h, agree5288 p q h]
theorem nonnegative5311 (p : Pattern) : 0 ≤ d5311 p :=
  nonnegative_ite (p 163) (nonnegative5293 p) (nonnegative5288 p)
def d5312 (p : Pattern) : Int := if p 162 then d5311 p else d5310 p
theorem agree5312 (p q : Pattern) (h : Agree support p q) : d5312 p = d5312 q := by
  simp only [d5312, h 162 (by decide), agree5311 p q h, agree5310 p q h]
theorem nonnegative5312 (p : Pattern) : 0 ≤ d5312 p :=
  nonnegative_ite (p 162) (nonnegative5311 p) (nonnegative5310 p)
def d5313 (p : Pattern) : Int := if p 182 then d12 p else d57 p
theorem agree5313 (p q : Pattern) (h : Agree support p q) : d5313 p = d5313 q := by
  simp only [d5313, h 182 (by decide), agree12 p q h, agree57 p q h]
theorem nonnegative5313 (p : Pattern) : 0 ≤ d5313 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative57 p)
def d5314 (p : Pattern) : Int := if p 163 then d5313 p else d5288 p
theorem agree5314 (p q : Pattern) (h : Agree support p q) : d5314 p = d5314 q := by
  simp only [d5314, h 163 (by decide), agree5313 p q h, agree5288 p q h]
theorem nonnegative5314 (p : Pattern) : 0 ≤ d5314 p :=
  nonnegative_ite (p 163) (nonnegative5313 p) (nonnegative5288 p)
def d5315 (p : Pattern) : Int := if p 182 then d12 p else d39 p
theorem agree5315 (p q : Pattern) (h : Agree support p q) : d5315 p = d5315 q := by
  simp only [d5315, h 182 (by decide), agree12 p q h, agree39 p q h]
theorem nonnegative5315 (p : Pattern) : 0 ≤ d5315 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative39 p)
def d5316 (p : Pattern) : Int := if p 163 then d12 p else d5315 p
theorem agree5316 (p q : Pattern) (h : Agree support p q) : d5316 p = d5316 q := by
  simp only [d5316, h 163 (by decide), agree12 p q h, agree5315 p q h]
theorem nonnegative5316 (p : Pattern) : 0 ≤ d5316 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5315 p)
def d5317 (p : Pattern) : Int := if p 162 then d5316 p else d5314 p
theorem agree5317 (p q : Pattern) (h : Agree support p q) : d5317 p = d5317 q := by
  simp only [d5317, h 162 (by decide), agree5316 p q h, agree5314 p q h]
theorem nonnegative5317 (p : Pattern) : 0 ≤ d5317 p :=
  nonnegative_ite (p 162) (nonnegative5316 p) (nonnegative5314 p)
def d5318 (p : Pattern) : Int := if p 161 then d5317 p else d5312 p
theorem agree5318 (p q : Pattern) (h : Agree support p q) : d5318 p = d5318 q := by
  simp only [d5318, h 161 (by decide), agree5317 p q h, agree5312 p q h]
theorem nonnegative5318 (p : Pattern) : 0 ≤ d5318 p :=
  nonnegative_ite (p 161) (nonnegative5317 p) (nonnegative5312 p)
def d5319 (p : Pattern) : Int := if p 160 then d5318 p else d5308 p
theorem agree5319 (p q : Pattern) (h : Agree support p q) : d5319 p = d5319 q := by
  simp only [d5319, h 160 (by decide), agree5318 p q h, agree5308 p q h]
theorem nonnegative5319 (p : Pattern) : 0 ≤ d5319 p :=
  nonnegative_ite (p 160) (nonnegative5318 p) (nonnegative5308 p)
def d5320 (p : Pattern) : Int := if p 141 then d5319 p else d5297 p
theorem agree5320 (p q : Pattern) (h : Agree support p q) : d5320 p = d5320 q := by
  simp only [d5320, h 141 (by decide), agree5319 p q h, agree5297 p q h]
theorem nonnegative5320 (p : Pattern) : 0 ≤ d5320 p :=
  nonnegative_ite (p 141) (nonnegative5319 p) (nonnegative5297 p)
def d5321 (p : Pattern) : Int := if p 182 then d5283 p else d34 p
theorem agree5321 (p q : Pattern) (h : Agree support p q) : d5321 p = d5321 q := by
  simp only [d5321, h 182 (by decide), agree5283 p q h, agree34 p q h]
theorem nonnegative5321 (p : Pattern) : 0 ≤ d5321 p :=
  nonnegative_ite (p 182) (nonnegative5283 p) (nonnegative34 p)
def d5322 (p : Pattern) : Int := if p 163 then d5321 p else d5298 p
theorem agree5322 (p q : Pattern) (h : Agree support p q) : d5322 p = d5322 q := by
  simp only [d5322, h 163 (by decide), agree5321 p q h, agree5298 p q h]
theorem nonnegative5322 (p : Pattern) : 0 ≤ d5322 p :=
  nonnegative_ite (p 163) (nonnegative5321 p) (nonnegative5298 p)
def d5323 (p : Pattern) : Int := if p 162 then d5306 p else d5322 p
theorem agree5323 (p q : Pattern) (h : Agree support p q) : d5323 p = d5323 q := by
  simp only [d5323, h 162 (by decide), agree5306 p q h, agree5322 p q h]
theorem nonnegative5323 (p : Pattern) : 0 ≤ d5323 p :=
  nonnegative_ite (p 162) (nonnegative5306 p) (nonnegative5322 p)
def d5324 (p : Pattern) : Int := if p 161 then d12 p else d5323 p
theorem agree5324 (p q : Pattern) (h : Agree support p q) : d5324 p = d5324 q := by
  simp only [d5324, h 161 (by decide), agree12 p q h, agree5323 p q h]
theorem nonnegative5324 (p : Pattern) : 0 ≤ d5324 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5323 p)
def d5325 (p : Pattern) : Int := if p 160 then d5324 p else d5280 p
theorem agree5325 (p q : Pattern) (h : Agree support p q) : d5325 p = d5325 q := by
  simp only [d5325, h 160 (by decide), agree5324 p q h, agree5280 p q h]
theorem nonnegative5325 (p : Pattern) : 0 ≤ d5325 p :=
  nonnegative_ite (p 160) (nonnegative5324 p) (nonnegative5280 p)
def d5326 (p : Pattern) : Int := if p 163 then d12 p else d5321 p
theorem agree5326 (p q : Pattern) (h : Agree support p q) : d5326 p = d5326 q := by
  simp only [d5326, h 163 (by decide), agree12 p q h, agree5321 p q h]
theorem nonnegative5326 (p : Pattern) : 0 ≤ d5326 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5321 p)
def d5327 (p : Pattern) : Int := if p 162 then d12 p else d5326 p
theorem agree5327 (p q : Pattern) (h : Agree support p q) : d5327 p = d5327 q := by
  simp only [d5327, h 162 (by decide), agree12 p q h, agree5326 p q h]
theorem nonnegative5327 (p : Pattern) : 0 ≤ d5327 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5326 p)
def d5328 (p : Pattern) : Int := if p 161 then d12 p else d5327 p
theorem agree5328 (p q : Pattern) (h : Agree support p q) : d5328 p = d5328 q := by
  simp only [d5328, h 161 (by decide), agree12 p q h, agree5327 p q h]
theorem nonnegative5328 (p : Pattern) : 0 ≤ d5328 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5327 p)
def d5329 (p : Pattern) : Int := if p 160 then d5328 p else d5308 p
theorem agree5329 (p q : Pattern) (h : Agree support p q) : d5329 p = d5329 q := by
  simp only [d5329, h 160 (by decide), agree5328 p q h, agree5308 p q h]
theorem nonnegative5329 (p : Pattern) : 0 ≤ d5329 p :=
  nonnegative_ite (p 160) (nonnegative5328 p) (nonnegative5308 p)
def d5330 (p : Pattern) : Int := if p 141 then d5329 p else d5325 p
theorem agree5330 (p q : Pattern) (h : Agree support p q) : d5330 p = d5330 q := by
  simp only [d5330, h 141 (by decide), agree5329 p q h, agree5325 p q h]
theorem nonnegative5330 (p : Pattern) : 0 ≤ d5330 p :=
  nonnegative_ite (p 141) (nonnegative5329 p) (nonnegative5325 p)
def d5331 (p : Pattern) : Int := if p 138 then d5330 p else d5320 p
theorem agree5331 (p q : Pattern) (h : Agree support p q) : d5331 p = d5331 q := by
  simp only [d5331, h 138 (by decide), agree5330 p q h, agree5320 p q h]
theorem nonnegative5331 (p : Pattern) : 0 ≤ d5331 p :=
  nonnegative_ite (p 138) (nonnegative5330 p) (nonnegative5320 p)
def d5332 (p : Pattern) : Int := if p 163 then d5305 p else d5277 p
theorem agree5332 (p q : Pattern) (h : Agree support p q) : d5332 p = d5332 q := by
  simp only [d5332, h 163 (by decide), agree5305 p q h, agree5277 p q h]
theorem nonnegative5332 (p : Pattern) : 0 ≤ d5332 p :=
  nonnegative_ite (p 163) (nonnegative5305 p) (nonnegative5277 p)
def d5333 (p : Pattern) : Int := if p 162 then d5306 p else d5332 p
theorem agree5333 (p q : Pattern) (h : Agree support p q) : d5333 p = d5333 q := by
  simp only [d5333, h 162 (by decide), agree5306 p q h, agree5332 p q h]
theorem nonnegative5333 (p : Pattern) : 0 ≤ d5333 p :=
  nonnegative_ite (p 162) (nonnegative5306 p) (nonnegative5332 p)
def d5334 (p : Pattern) : Int := if p 162 then d12 p else d5306 p
theorem agree5334 (p q : Pattern) (h : Agree support p q) : d5334 p = d5334 q := by
  simp only [d5334, h 162 (by decide), agree12 p q h, agree5306 p q h]
theorem nonnegative5334 (p : Pattern) : 0 ≤ d5334 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5306 p)
def d5335 (p : Pattern) : Int := if p 161 then d5334 p else d5333 p
theorem agree5335 (p q : Pattern) (h : Agree support p q) : d5335 p = d5335 q := by
  simp only [d5335, h 161 (by decide), agree5334 p q h, agree5333 p q h]
theorem nonnegative5335 (p : Pattern) : 0 ≤ d5335 p :=
  nonnegative_ite (p 161) (nonnegative5334 p) (nonnegative5333 p)
def d5336 (p : Pattern) : Int := if p 161 then d12 p else d5334 p
theorem agree5336 (p q : Pattern) (h : Agree support p q) : d5336 p = d5336 q := by
  simp only [d5336, h 161 (by decide), agree12 p q h, agree5334 p q h]
theorem nonnegative5336 (p : Pattern) : 0 ≤ d5336 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5334 p)
def d5337 (p : Pattern) : Int := if p 160 then d5336 p else d5335 p
theorem agree5337 (p q : Pattern) (h : Agree support p q) : d5337 p = d5337 q := by
  simp only [d5337, h 160 (by decide), agree5336 p q h, agree5335 p q h]
theorem nonnegative5337 (p : Pattern) : 0 ≤ d5337 p :=
  nonnegative_ite (p 160) (nonnegative5336 p) (nonnegative5335 p)
def d5338 (p : Pattern) : Int := if p 160 then d12 p else d5336 p
theorem agree5338 (p q : Pattern) (h : Agree support p q) : d5338 p = d5338 q := by
  simp only [d5338, h 160 (by decide), agree12 p q h, agree5336 p q h]
theorem nonnegative5338 (p : Pattern) : 0 ≤ d5338 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative5336 p)
def d5339 (p : Pattern) : Int := if p 141 then d5338 p else d5337 p
theorem agree5339 (p q : Pattern) (h : Agree support p q) : d5339 p = d5339 q := by
  simp only [d5339, h 141 (by decide), agree5338 p q h, agree5337 p q h]
theorem nonnegative5339 (p : Pattern) : 0 ≤ d5339 p :=
  nonnegative_ite (p 141) (nonnegative5338 p) (nonnegative5337 p)
def d5340 (p : Pattern) : Int := if p 138 then d5339 p else d5330 p
theorem agree5340 (p q : Pattern) (h : Agree support p q) : d5340 p = d5340 q := by
  simp only [d5340, h 138 (by decide), agree5339 p q h, agree5330 p q h]
theorem nonnegative5340 (p : Pattern) : 0 ≤ d5340 p :=
  nonnegative_ite (p 138) (nonnegative5339 p) (nonnegative5330 p)
def d5341 (p : Pattern) : Int := if p 116 then d5340 p else d5331 p
theorem agree5341 (p q : Pattern) (h : Agree support p q) : d5341 p = d5341 q := by
  simp only [d5341, h 116 (by decide), agree5340 p q h, agree5331 p q h]
theorem nonnegative5341 (p : Pattern) : 0 ≤ d5341 p :=
  nonnegative_ite (p 116) (nonnegative5340 p) (nonnegative5331 p)
def d5342 (p : Pattern) : Int := if p 138 then d12 p else d5330 p
theorem agree5342 (p q : Pattern) (h : Agree support p q) : d5342 p = d5342 q := by
  simp only [d5342, h 138 (by decide), agree12 p q h, agree5330 p q h]
theorem nonnegative5342 (p : Pattern) : 0 ≤ d5342 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5330 p)
def d5343 (p : Pattern) : Int := if p 116 then d5342 p else d5331 p
theorem agree5343 (p q : Pattern) (h : Agree support p q) : d5343 p = d5343 q := by
  simp only [d5343, h 116 (by decide), agree5342 p q h, agree5331 p q h]
theorem nonnegative5343 (p : Pattern) : 0 ≤ d5343 p :=
  nonnegative_ite (p 116) (nonnegative5342 p) (nonnegative5331 p)
def d5344 (p : Pattern) : Int := if p 115 then d5343 p else d5341 p
theorem agree5344 (p q : Pattern) (h : Agree support p q) : d5344 p = d5344 q := by
  simp only [d5344, h 115 (by decide), agree5343 p q h, agree5341 p q h]
theorem nonnegative5344 (p : Pattern) : 0 ≤ d5344 p :=
  nonnegative_ite (p 115) (nonnegative5343 p) (nonnegative5341 p)
def d5345 (p : Pattern) : Int := if p 204 then d12 p else d102 p
theorem agree5345 (p q : Pattern) (h : Agree support p q) : d5345 p = d5345 q := by
  simp only [d5345, h 204 (by decide), agree12 p q h, agree102 p q h]
theorem nonnegative5345 (p : Pattern) : 0 ≤ d5345 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative102 p)
def d5346 (p : Pattern) : Int := if p 182 then d5345 p else d102 p
theorem agree5346 (p q : Pattern) (h : Agree support p q) : d5346 p = d5346 q := by
  simp only [d5346, h 182 (by decide), agree5345 p q h, agree102 p q h]
theorem nonnegative5346 (p : Pattern) : 0 ≤ d5346 p :=
  nonnegative_ite (p 182) (nonnegative5345 p) (nonnegative102 p)
def d5347 (p : Pattern) : Int := if p 204 then d12 p else d106 p
theorem agree5347 (p q : Pattern) (h : Agree support p q) : d5347 p = d5347 q := by
  simp only [d5347, h 204 (by decide), agree12 p q h, agree106 p q h]
theorem nonnegative5347 (p : Pattern) : 0 ≤ d5347 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative106 p)
def d5348 (p : Pattern) : Int := if p 182 then d5347 p else d106 p
theorem agree5348 (p q : Pattern) (h : Agree support p q) : d5348 p = d5348 q := by
  simp only [d5348, h 182 (by decide), agree5347 p q h, agree106 p q h]
theorem nonnegative5348 (p : Pattern) : 0 ≤ d5348 p :=
  nonnegative_ite (p 182) (nonnegative5347 p) (nonnegative106 p)
def d5349 (p : Pattern) : Int := if p 163 then d5348 p else d5346 p
theorem agree5349 (p q : Pattern) (h : Agree support p q) : d5349 p = d5349 q := by
  simp only [d5349, h 163 (by decide), agree5348 p q h, agree5346 p q h]
theorem nonnegative5349 (p : Pattern) : 0 ≤ d5349 p :=
  nonnegative_ite (p 163) (nonnegative5348 p) (nonnegative5346 p)
def d5350 (p : Pattern) : Int := if p 162 then d5349 p else d5346 p
theorem agree5350 (p q : Pattern) (h : Agree support p q) : d5350 p = d5350 q := by
  simp only [d5350, h 162 (by decide), agree5349 p q h, agree5346 p q h]
theorem nonnegative5350 (p : Pattern) : 0 ≤ d5350 p :=
  nonnegative_ite (p 162) (nonnegative5349 p) (nonnegative5346 p)
def d5351 (p : Pattern) : Int := if p 163 then d12 p else d5303 p
theorem agree5351 (p q : Pattern) (h : Agree support p q) : d5351 p = d5351 q := by
  simp only [d5351, h 163 (by decide), agree12 p q h, agree5303 p q h]
theorem nonnegative5351 (p : Pattern) : 0 ≤ d5351 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5303 p)
def d5352 (p : Pattern) : Int := if p 162 then d5351 p else d5349 p
theorem agree5352 (p q : Pattern) (h : Agree support p q) : d5352 p = d5352 q := by
  simp only [d5352, h 162 (by decide), agree5351 p q h, agree5349 p q h]
theorem nonnegative5352 (p : Pattern) : 0 ≤ d5352 p :=
  nonnegative_ite (p 162) (nonnegative5351 p) (nonnegative5349 p)
def d5353 (p : Pattern) : Int := if p 161 then d5352 p else d5350 p
theorem agree5353 (p q : Pattern) (h : Agree support p q) : d5353 p = d5353 q := by
  simp only [d5353, h 161 (by decide), agree5352 p q h, agree5350 p q h]
theorem nonnegative5353 (p : Pattern) : 0 ≤ d5353 p :=
  nonnegative_ite (p 161) (nonnegative5352 p) (nonnegative5350 p)
def d5354 (p : Pattern) : Int := if p 204 then d12 p else d115 p
theorem agree5354 (p q : Pattern) (h : Agree support p q) : d5354 p = d5354 q := by
  simp only [d5354, h 204 (by decide), agree12 p q h, agree115 p q h]
theorem nonnegative5354 (p : Pattern) : 0 ≤ d5354 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative115 p)
def d5355 (p : Pattern) : Int := if p 182 then d5354 p else d102 p
theorem agree5355 (p q : Pattern) (h : Agree support p q) : d5355 p = d5355 q := by
  simp only [d5355, h 182 (by decide), agree5354 p q h, agree102 p q h]
theorem nonnegative5355 (p : Pattern) : 0 ≤ d5355 p :=
  nonnegative_ite (p 182) (nonnegative5354 p) (nonnegative102 p)
def d5356 (p : Pattern) : Int := if p 204 then d12 p else d119 p
theorem agree5356 (p q : Pattern) (h : Agree support p q) : d5356 p = d5356 q := by
  simp only [d5356, h 204 (by decide), agree12 p q h, agree119 p q h]
theorem nonnegative5356 (p : Pattern) : 0 ≤ d5356 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative119 p)
def d5357 (p : Pattern) : Int := if p 182 then d5356 p else d102 p
theorem agree5357 (p q : Pattern) (h : Agree support p q) : d5357 p = d5357 q := by
  simp only [d5357, h 182 (by decide), agree5356 p q h, agree102 p q h]
theorem nonnegative5357 (p : Pattern) : 0 ≤ d5357 p :=
  nonnegative_ite (p 182) (nonnegative5356 p) (nonnegative102 p)
def d5358 (p : Pattern) : Int := if p 163 then d5357 p else d5355 p
theorem agree5358 (p q : Pattern) (h : Agree support p q) : d5358 p = d5358 q := by
  simp only [d5358, h 163 (by decide), agree5357 p q h, agree5355 p q h]
theorem nonnegative5358 (p : Pattern) : 0 ≤ d5358 p :=
  nonnegative_ite (p 163) (nonnegative5357 p) (nonnegative5355 p)
def d5359 (p : Pattern) : Int := if p 182 then d12 p else d102 p
theorem agree5359 (p q : Pattern) (h : Agree support p q) : d5359 p = d5359 q := by
  simp only [d5359, h 182 (by decide), agree12 p q h, agree102 p q h]
theorem nonnegative5359 (p : Pattern) : 0 ≤ d5359 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative102 p)
def d5360 (p : Pattern) : Int := if p 182 then d12 p else d106 p
theorem agree5360 (p q : Pattern) (h : Agree support p q) : d5360 p = d5360 q := by
  simp only [d5360, h 182 (by decide), agree12 p q h, agree106 p q h]
theorem nonnegative5360 (p : Pattern) : 0 ≤ d5360 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative106 p)
def d5361 (p : Pattern) : Int := if p 163 then d5360 p else d5359 p
theorem agree5361 (p q : Pattern) (h : Agree support p q) : d5361 p = d5361 q := by
  simp only [d5361, h 163 (by decide), agree5360 p q h, agree5359 p q h]
theorem nonnegative5361 (p : Pattern) : 0 ≤ d5361 p :=
  nonnegative_ite (p 163) (nonnegative5360 p) (nonnegative5359 p)
def d5362 (p : Pattern) : Int := if p 162 then d5361 p else d5358 p
theorem agree5362 (p q : Pattern) (h : Agree support p q) : d5362 p = d5362 q := by
  simp only [d5362, h 162 (by decide), agree5361 p q h, agree5358 p q h]
theorem nonnegative5362 (p : Pattern) : 0 ≤ d5362 p :=
  nonnegative_ite (p 162) (nonnegative5361 p) (nonnegative5358 p)
def d5363 (p : Pattern) : Int := if p 163 then d12 p else d5313 p
theorem agree5363 (p q : Pattern) (h : Agree support p q) : d5363 p = d5363 q := by
  simp only [d5363, h 163 (by decide), agree12 p q h, agree5313 p q h]
theorem nonnegative5363 (p : Pattern) : 0 ≤ d5363 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5313 p)
def d5364 (p : Pattern) : Int := if p 162 then d5363 p else d5361 p
theorem agree5364 (p q : Pattern) (h : Agree support p q) : d5364 p = d5364 q := by
  simp only [d5364, h 162 (by decide), agree5363 p q h, agree5361 p q h]
theorem nonnegative5364 (p : Pattern) : 0 ≤ d5364 p :=
  nonnegative_ite (p 162) (nonnegative5363 p) (nonnegative5361 p)
def d5365 (p : Pattern) : Int := if p 161 then d5364 p else d5362 p
theorem agree5365 (p q : Pattern) (h : Agree support p q) : d5365 p = d5365 q := by
  simp only [d5365, h 161 (by decide), agree5364 p q h, agree5362 p q h]
theorem nonnegative5365 (p : Pattern) : 0 ≤ d5365 p :=
  nonnegative_ite (p 161) (nonnegative5364 p) (nonnegative5362 p)
def d5366 (p : Pattern) : Int := if p 160 then d5365 p else d5353 p
theorem agree5366 (p q : Pattern) (h : Agree support p q) : d5366 p = d5366 q := by
  simp only [d5366, h 160 (by decide), agree5365 p q h, agree5353 p q h]
theorem nonnegative5366 (p : Pattern) : 0 ≤ d5366 p :=
  nonnegative_ite (p 160) (nonnegative5365 p) (nonnegative5353 p)
def d5367 (p : Pattern) : Int := if p 182 then d5354 p else d115 p
theorem agree5367 (p q : Pattern) (h : Agree support p q) : d5367 p = d5367 q := by
  simp only [d5367, h 182 (by decide), agree5354 p q h, agree115 p q h]
theorem nonnegative5367 (p : Pattern) : 0 ≤ d5367 p :=
  nonnegative_ite (p 182) (nonnegative5354 p) (nonnegative115 p)
def d5368 (p : Pattern) : Int := if p 163 then d5367 p else d5346 p
theorem agree5368 (p q : Pattern) (h : Agree support p q) : d5368 p = d5368 q := by
  simp only [d5368, h 163 (by decide), agree5367 p q h, agree5346 p q h]
theorem nonnegative5368 (p : Pattern) : 0 ≤ d5368 p :=
  nonnegative_ite (p 163) (nonnegative5367 p) (nonnegative5346 p)
def d5369 (p : Pattern) : Int := if p 163 then d5303 p else d5348 p
theorem agree5369 (p q : Pattern) (h : Agree support p q) : d5369 p = d5369 q := by
  simp only [d5369, h 163 (by decide), agree5303 p q h, agree5348 p q h]
theorem nonnegative5369 (p : Pattern) : 0 ≤ d5369 p :=
  nonnegative_ite (p 163) (nonnegative5303 p) (nonnegative5348 p)
def d5370 (p : Pattern) : Int := if p 162 then d5369 p else d5368 p
theorem agree5370 (p q : Pattern) (h : Agree support p q) : d5370 p = d5370 q := by
  simp only [d5370, h 162 (by decide), agree5369 p q h, agree5368 p q h]
theorem nonnegative5370 (p : Pattern) : 0 ≤ d5370 p :=
  nonnegative_ite (p 162) (nonnegative5369 p) (nonnegative5368 p)
def d5371 (p : Pattern) : Int := if p 163 then d5305 p else d5348 p
theorem agree5371 (p q : Pattern) (h : Agree support p q) : d5371 p = d5371 q := by
  simp only [d5371, h 163 (by decide), agree5305 p q h, agree5348 p q h]
theorem nonnegative5371 (p : Pattern) : 0 ≤ d5371 p :=
  nonnegative_ite (p 163) (nonnegative5305 p) (nonnegative5348 p)
def d5372 (p : Pattern) : Int := if p 162 then d12 p else d5371 p
theorem agree5372 (p q : Pattern) (h : Agree support p q) : d5372 p = d5372 q := by
  simp only [d5372, h 162 (by decide), agree12 p q h, agree5371 p q h]
theorem nonnegative5372 (p : Pattern) : 0 ≤ d5372 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5371 p)
def d5373 (p : Pattern) : Int := if p 161 then d5372 p else d5370 p
theorem agree5373 (p q : Pattern) (h : Agree support p q) : d5373 p = d5373 q := by
  simp only [d5373, h 161 (by decide), agree5372 p q h, agree5370 p q h]
theorem nonnegative5373 (p : Pattern) : 0 ≤ d5373 p :=
  nonnegative_ite (p 161) (nonnegative5372 p) (nonnegative5370 p)
def d5374 (p : Pattern) : Int := if p 182 then d12 p else d115 p
theorem agree5374 (p q : Pattern) (h : Agree support p q) : d5374 p = d5374 q := by
  simp only [d5374, h 182 (by decide), agree12 p q h, agree115 p q h]
theorem nonnegative5374 (p : Pattern) : 0 ≤ d5374 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative115 p)
def d5375 (p : Pattern) : Int := if p 163 then d5374 p else d5357 p
theorem agree5375 (p q : Pattern) (h : Agree support p q) : d5375 p = d5375 q := by
  simp only [d5375, h 163 (by decide), agree5374 p q h, agree5357 p q h]
theorem nonnegative5375 (p : Pattern) : 0 ≤ d5375 p :=
  nonnegative_ite (p 163) (nonnegative5374 p) (nonnegative5357 p)
def d5376 (p : Pattern) : Int := if p 163 then d5313 p else d5360 p
theorem agree5376 (p q : Pattern) (h : Agree support p q) : d5376 p = d5376 q := by
  simp only [d5376, h 163 (by decide), agree5313 p q h, agree5360 p q h]
theorem nonnegative5376 (p : Pattern) : 0 ≤ d5376 p :=
  nonnegative_ite (p 163) (nonnegative5313 p) (nonnegative5360 p)
def d5377 (p : Pattern) : Int := if p 162 then d5376 p else d5375 p
theorem agree5377 (p q : Pattern) (h : Agree support p q) : d5377 p = d5377 q := by
  simp only [d5377, h 162 (by decide), agree5376 p q h, agree5375 p q h]
theorem nonnegative5377 (p : Pattern) : 0 ≤ d5377 p :=
  nonnegative_ite (p 162) (nonnegative5376 p) (nonnegative5375 p)
def d5378 (p : Pattern) : Int := if p 163 then d5315 p else d5360 p
theorem agree5378 (p q : Pattern) (h : Agree support p q) : d5378 p = d5378 q := by
  simp only [d5378, h 163 (by decide), agree5315 p q h, agree5360 p q h]
theorem nonnegative5378 (p : Pattern) : 0 ≤ d5378 p :=
  nonnegative_ite (p 163) (nonnegative5315 p) (nonnegative5360 p)
def d5379 (p : Pattern) : Int := if p 162 then d12 p else d5378 p
theorem agree5379 (p q : Pattern) (h : Agree support p q) : d5379 p = d5379 q := by
  simp only [d5379, h 162 (by decide), agree12 p q h, agree5378 p q h]
theorem nonnegative5379 (p : Pattern) : 0 ≤ d5379 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5378 p)
def d5380 (p : Pattern) : Int := if p 161 then d5379 p else d5377 p
theorem agree5380 (p q : Pattern) (h : Agree support p q) : d5380 p = d5380 q := by
  simp only [d5380, h 161 (by decide), agree5379 p q h, agree5377 p q h]
theorem nonnegative5380 (p : Pattern) : 0 ≤ d5380 p :=
  nonnegative_ite (p 161) (nonnegative5379 p) (nonnegative5377 p)
def d5381 (p : Pattern) : Int := if p 160 then d5380 p else d5373 p
theorem agree5381 (p q : Pattern) (h : Agree support p q) : d5381 p = d5381 q := by
  simp only [d5381, h 160 (by decide), agree5380 p q h, agree5373 p q h]
theorem nonnegative5381 (p : Pattern) : 0 ≤ d5381 p :=
  nonnegative_ite (p 160) (nonnegative5380 p) (nonnegative5373 p)
def d5382 (p : Pattern) : Int := if p 141 then d5381 p else d5366 p
theorem agree5382 (p q : Pattern) (h : Agree support p q) : d5382 p = d5382 q := by
  simp only [d5382, h 141 (by decide), agree5381 p q h, agree5366 p q h]
theorem nonnegative5382 (p : Pattern) : 0 ≤ d5382 p :=
  nonnegative_ite (p 141) (nonnegative5381 p) (nonnegative5366 p)
def d5383 (p : Pattern) : Int := if p 182 then d5356 p else d119 p
theorem agree5383 (p q : Pattern) (h : Agree support p q) : d5383 p = d5383 q := by
  simp only [d5383, h 182 (by decide), agree5356 p q h, agree119 p q h]
theorem nonnegative5383 (p : Pattern) : 0 ≤ d5383 p :=
  nonnegative_ite (p 182) (nonnegative5356 p) (nonnegative119 p)
def d5384 (p : Pattern) : Int := if p 163 then d5383 p else d5367 p
theorem agree5384 (p q : Pattern) (h : Agree support p q) : d5384 p = d5384 q := by
  simp only [d5384, h 163 (by decide), agree5383 p q h, agree5367 p q h]
theorem nonnegative5384 (p : Pattern) : 0 ≤ d5384 p :=
  nonnegative_ite (p 163) (nonnegative5383 p) (nonnegative5367 p)
def d5385 (p : Pattern) : Int := if p 162 then d12 p else d5384 p
theorem agree5385 (p q : Pattern) (h : Agree support p q) : d5385 p = d5385 q := by
  simp only [d5385, h 162 (by decide), agree12 p q h, agree5384 p q h]
theorem nonnegative5385 (p : Pattern) : 0 ≤ d5385 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5384 p)
def d5386 (p : Pattern) : Int := if p 161 then d12 p else d5385 p
theorem agree5386 (p q : Pattern) (h : Agree support p q) : d5386 p = d5386 q := by
  simp only [d5386, h 161 (by decide), agree12 p q h, agree5385 p q h]
theorem nonnegative5386 (p : Pattern) : 0 ≤ d5386 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5385 p)
def d5387 (p : Pattern) : Int := if p 160 then d5386 p else d5353 p
theorem agree5387 (p q : Pattern) (h : Agree support p q) : d5387 p = d5387 q := by
  simp only [d5387, h 160 (by decide), agree5386 p q h, agree5353 p q h]
theorem nonnegative5387 (p : Pattern) : 0 ≤ d5387 p :=
  nonnegative_ite (p 160) (nonnegative5386 p) (nonnegative5353 p)
def d5388 (p : Pattern) : Int := if p 163 then d12 p else d5383 p
theorem agree5388 (p q : Pattern) (h : Agree support p q) : d5388 p = d5388 q := by
  simp only [d5388, h 163 (by decide), agree12 p q h, agree5383 p q h]
theorem nonnegative5388 (p : Pattern) : 0 ≤ d5388 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5383 p)
def d5389 (p : Pattern) : Int := if p 162 then d12 p else d5388 p
theorem agree5389 (p q : Pattern) (h : Agree support p q) : d5389 p = d5389 q := by
  simp only [d5389, h 162 (by decide), agree12 p q h, agree5388 p q h]
theorem nonnegative5389 (p : Pattern) : 0 ≤ d5389 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5388 p)
def d5390 (p : Pattern) : Int := if p 161 then d12 p else d5389 p
theorem agree5390 (p q : Pattern) (h : Agree support p q) : d5390 p = d5390 q := by
  simp only [d5390, h 161 (by decide), agree12 p q h, agree5389 p q h]
theorem nonnegative5390 (p : Pattern) : 0 ≤ d5390 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5389 p)
def d5391 (p : Pattern) : Int := if p 160 then d5390 p else d5373 p
theorem agree5391 (p q : Pattern) (h : Agree support p q) : d5391 p = d5391 q := by
  simp only [d5391, h 160 (by decide), agree5390 p q h, agree5373 p q h]
theorem nonnegative5391 (p : Pattern) : 0 ≤ d5391 p :=
  nonnegative_ite (p 160) (nonnegative5390 p) (nonnegative5373 p)
def d5392 (p : Pattern) : Int := if p 141 then d5391 p else d5387 p
theorem agree5392 (p q : Pattern) (h : Agree support p q) : d5392 p = d5392 q := by
  simp only [d5392, h 141 (by decide), agree5391 p q h, agree5387 p q h]
theorem nonnegative5392 (p : Pattern) : 0 ≤ d5392 p :=
  nonnegative_ite (p 141) (nonnegative5391 p) (nonnegative5387 p)
def d5393 (p : Pattern) : Int := if p 138 then d5392 p else d5382 p
theorem agree5393 (p q : Pattern) (h : Agree support p q) : d5393 p = d5393 q := by
  simp only [d5393, h 138 (by decide), agree5392 p q h, agree5382 p q h]
theorem nonnegative5393 (p : Pattern) : 0 ≤ d5393 p :=
  nonnegative_ite (p 138) (nonnegative5392 p) (nonnegative5382 p)
def d5394 (p : Pattern) : Int := if p 162 then d12 p else d5351 p
theorem agree5394 (p q : Pattern) (h : Agree support p q) : d5394 p = d5394 q := by
  simp only [d5394, h 162 (by decide), agree12 p q h, agree5351 p q h]
theorem nonnegative5394 (p : Pattern) : 0 ≤ d5394 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5351 p)
def d5395 (p : Pattern) : Int := if p 161 then d12 p else d5394 p
theorem agree5395 (p q : Pattern) (h : Agree support p q) : d5395 p = d5395 q := by
  simp only [d5395, h 161 (by decide), agree12 p q h, agree5394 p q h]
theorem nonnegative5395 (p : Pattern) : 0 ≤ d5395 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5394 p)
def d5396 (p : Pattern) : Int := if p 160 then d12 p else d5395 p
theorem agree5396 (p q : Pattern) (h : Agree support p q) : d5396 p = d5396 q := by
  simp only [d5396, h 160 (by decide), agree12 p q h, agree5395 p q h]
theorem nonnegative5396 (p : Pattern) : 0 ≤ d5396 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative5395 p)
def d5397 (p : Pattern) : Int := if p 141 then d12 p else d5396 p
theorem agree5397 (p q : Pattern) (h : Agree support p q) : d5397 p = d5397 q := by
  simp only [d5397, h 141 (by decide), agree12 p q h, agree5396 p q h]
theorem nonnegative5397 (p : Pattern) : 0 ≤ d5397 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative5396 p)
def d5398 (p : Pattern) : Int := if p 138 then d5397 p else d5392 p
theorem agree5398 (p q : Pattern) (h : Agree support p q) : d5398 p = d5398 q := by
  simp only [d5398, h 138 (by decide), agree5397 p q h, agree5392 p q h]
theorem nonnegative5398 (p : Pattern) : 0 ≤ d5398 p :=
  nonnegative_ite (p 138) (nonnegative5397 p) (nonnegative5392 p)
def d5399 (p : Pattern) : Int := if p 116 then d5398 p else d5393 p
theorem agree5399 (p q : Pattern) (h : Agree support p q) : d5399 p = d5399 q := by
  simp only [d5399, h 116 (by decide), agree5398 p q h, agree5393 p q h]
theorem nonnegative5399 (p : Pattern) : 0 ≤ d5399 p :=
  nonnegative_ite (p 116) (nonnegative5398 p) (nonnegative5393 p)
end NetHack.Sokoban22Refined85
