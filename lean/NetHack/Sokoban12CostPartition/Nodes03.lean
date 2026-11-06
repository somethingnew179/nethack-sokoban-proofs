/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Nodes02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d360 (p : Pattern) : Int := if p 134 then d2 p else d76 p
theorem agree360 (p q : Pattern) (h : Agree support p q) : d360 p = d360 q := by
  simp only [d360, h 134 (by decide), agree2 p q h, agree76 p q h]
theorem nonnegative360 (p : Pattern) : 0 ≤ d360 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative76 p)
def d361 (p : Pattern) : Int := if p 134 then d2 p else d221 p
theorem agree361 (p q : Pattern) (h : Agree support p q) : d361 p = d361 q := by
  simp only [d361, h 134 (by decide), agree2 p q h, agree221 p q h]
theorem nonnegative361 (p : Pattern) : 0 ≤ d361 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative221 p)
def d362 (p : Pattern) : Int := if p 133 then d361 p else d360 p
theorem agree362 (p q : Pattern) (h : Agree support p q) : d362 p = d362 q := by
  simp only [d362, h 133 (by decide), agree361 p q h, agree360 p q h]
theorem nonnegative362 (p : Pattern) : 0 ≤ d362 p :=
  nonnegative_ite (p 133) (nonnegative361 p) (nonnegative360 p)
def d363 (p : Pattern) : Int := if p 133 then d2 p else d361 p
theorem agree363 (p q : Pattern) (h : Agree support p q) : d363 p = d363 q := by
  simp only [d363, h 133 (by decide), agree2 p q h, agree361 p q h]
theorem nonnegative363 (p : Pattern) : 0 ≤ d363 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative361 p)
def d364 (p : Pattern) : Int := if p 132 then d363 p else d362 p
theorem agree364 (p q : Pattern) (h : Agree support p q) : d364 p = d364 q := by
  simp only [d364, h 132 (by decide), agree363 p q h, agree362 p q h]
theorem nonnegative364 (p : Pattern) : 0 ≤ d364 p :=
  nonnegative_ite (p 132) (nonnegative363 p) (nonnegative362 p)
def d365 (p : Pattern) : Int := if p 108 then d364 p else d359 p
theorem agree365 (p q : Pattern) (h : Agree support p q) : d365 p = d365 q := by
  simp only [d365, h 108 (by decide), agree364 p q h, agree359 p q h]
theorem nonnegative365 (p : Pattern) : 0 ≤ d365 p :=
  nonnegative_ite (p 108) (nonnegative364 p) (nonnegative359 p)
def d366 (p : Pattern) : Int := if p 133 then d231 p else d227 p
theorem agree366 (p q : Pattern) (h : Agree support p q) : d366 p = d366 q := by
  simp only [d366, h 133 (by decide), agree231 p q h, agree227 p q h]
theorem nonnegative366 (p : Pattern) : 0 ≤ d366 p :=
  nonnegative_ite (p 133) (nonnegative231 p) (nonnegative227 p)
def d367 (p : Pattern) : Int := if p 133 then d66 p else d231 p
theorem agree367 (p q : Pattern) (h : Agree support p q) : d367 p = d367 q := by
  simp only [d367, h 133 (by decide), agree66 p q h, agree231 p q h]
theorem nonnegative367 (p : Pattern) : 0 ≤ d367 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative231 p)
def d368 (p : Pattern) : Int := if p 132 then d367 p else d366 p
theorem agree368 (p q : Pattern) (h : Agree support p q) : d368 p = d368 q := by
  simp only [d368, h 132 (by decide), agree367 p q h, agree366 p q h]
theorem nonnegative368 (p : Pattern) : 0 ≤ d368 p :=
  nonnegative_ite (p 132) (nonnegative367 p) (nonnegative366 p)
def d369 (p : Pattern) : Int := if p 134 then d66 p else d227 p
theorem agree369 (p q : Pattern) (h : Agree support p q) : d369 p = d369 q := by
  simp only [d369, h 134 (by decide), agree66 p q h, agree227 p q h]
theorem nonnegative369 (p : Pattern) : 0 ≤ d369 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative227 p)
def d370 (p : Pattern) : Int := if p 134 then d66 p else d231 p
theorem agree370 (p q : Pattern) (h : Agree support p q) : d370 p = d370 q := by
  simp only [d370, h 134 (by decide), agree66 p q h, agree231 p q h]
theorem nonnegative370 (p : Pattern) : 0 ≤ d370 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative231 p)
def d371 (p : Pattern) : Int := if p 133 then d370 p else d369 p
theorem agree371 (p q : Pattern) (h : Agree support p q) : d371 p = d371 q := by
  simp only [d371, h 133 (by decide), agree370 p q h, agree369 p q h]
theorem nonnegative371 (p : Pattern) : 0 ≤ d371 p :=
  nonnegative_ite (p 133) (nonnegative370 p) (nonnegative369 p)
def d372 (p : Pattern) : Int := if p 133 then d66 p else d370 p
theorem agree372 (p q : Pattern) (h : Agree support p q) : d372 p = d372 q := by
  simp only [d372, h 133 (by decide), agree66 p q h, agree370 p q h]
theorem nonnegative372 (p : Pattern) : 0 ≤ d372 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative370 p)
def d373 (p : Pattern) : Int := if p 132 then d372 p else d371 p
theorem agree373 (p q : Pattern) (h : Agree support p q) : d373 p = d373 q := by
  simp only [d373, h 132 (by decide), agree372 p q h, agree371 p q h]
theorem nonnegative373 (p : Pattern) : 0 ≤ d373 p :=
  nonnegative_ite (p 132) (nonnegative372 p) (nonnegative371 p)
def d374 (p : Pattern) : Int := if p 108 then d373 p else d368 p
theorem agree374 (p q : Pattern) (h : Agree support p q) : d374 p = d374 q := by
  simp only [d374, h 108 (by decide), agree373 p q h, agree368 p q h]
theorem nonnegative374 (p : Pattern) : 0 ≤ d374 p :=
  nonnegative_ite (p 108) (nonnegative373 p) (nonnegative368 p)
def d375 (p : Pattern) : Int := if p 168 then d261 p else d56 p
theorem agree375 (p q : Pattern) (h : Agree support p q) : d375 p = d375 q := by
  simp only [d375, h 168 (by decide), agree261 p q h, agree56 p q h]
theorem nonnegative375 (p : Pattern) : 0 ≤ d375 p :=
  nonnegative_ite (p 168) (nonnegative261 p) (nonnegative56 p)
def d376 (p : Pattern) : Int := if p 160 then d375 p else d21 p
theorem agree376 (p q : Pattern) (h : Agree support p q) : d376 p = d376 q := by
  simp only [d376, h 160 (by decide), agree375 p q h, agree21 p q h]
theorem nonnegative376 (p : Pattern) : 0 ≤ d376 p :=
  nonnegative_ite (p 160) (nonnegative375 p) (nonnegative21 p)
def d377 (p : Pattern) : Int := if p 168 then d265 p else d56 p
theorem agree377 (p q : Pattern) (h : Agree support p q) : d377 p = d377 q := by
  simp only [d377, h 168 (by decide), agree265 p q h, agree56 p q h]
theorem nonnegative377 (p : Pattern) : 0 ≤ d377 p :=
  nonnegative_ite (p 168) (nonnegative265 p) (nonnegative56 p)
def d378 (p : Pattern) : Int := if p 160 then d377 p else d22 p
theorem agree378 (p q : Pattern) (h : Agree support p q) : d378 p = d378 q := by
  simp only [d378, h 160 (by decide), agree377 p q h, agree22 p q h]
theorem nonnegative378 (p : Pattern) : 0 ≤ d378 p :=
  nonnegative_ite (p 160) (nonnegative377 p) (nonnegative22 p)
def d379 (p : Pattern) : Int := if p 141 then d378 p else d376 p
theorem agree379 (p q : Pattern) (h : Agree support p q) : d379 p = d379 q := by
  simp only [d379, h 141 (by decide), agree378 p q h, agree376 p q h]
theorem nonnegative379 (p : Pattern) : 0 ≤ d379 p :=
  nonnegative_ite (p 141) (nonnegative378 p) (nonnegative376 p)
def d380 (p : Pattern) : Int := if p 168 then d260 p else d55 p
theorem agree380 (p q : Pattern) (h : Agree support p q) : d380 p = d380 q := by
  simp only [d380, h 168 (by decide), agree260 p q h, agree55 p q h]
theorem nonnegative380 (p : Pattern) : 0 ≤ d380 p :=
  nonnegative_ite (p 168) (nonnegative260 p) (nonnegative55 p)
def d381 (p : Pattern) : Int := if p 160 then d380 p else d21 p
theorem agree381 (p q : Pattern) (h : Agree support p q) : d381 p = d381 q := by
  simp only [d381, h 160 (by decide), agree380 p q h, agree21 p q h]
theorem nonnegative381 (p : Pattern) : 0 ≤ d381 p :=
  nonnegative_ite (p 160) (nonnegative380 p) (nonnegative21 p)
def d382 (p : Pattern) : Int := if p 168 then d272 p else d120 p
theorem agree382 (p q : Pattern) (h : Agree support p q) : d382 p = d382 q := by
  simp only [d382, h 168 (by decide), agree272 p q h, agree120 p q h]
theorem nonnegative382 (p : Pattern) : 0 ≤ d382 p :=
  nonnegative_ite (p 168) (nonnegative272 p) (nonnegative120 p)
def d383 (p : Pattern) : Int := if p 160 then d380 p else d382 p
theorem agree383 (p q : Pattern) (h : Agree support p q) : d383 p = d383 q := by
  simp only [d383, h 160 (by decide), agree380 p q h, agree382 p q h]
theorem nonnegative383 (p : Pattern) : 0 ≤ d383 p :=
  nonnegative_ite (p 160) (nonnegative380 p) (nonnegative382 p)
def d384 (p : Pattern) : Int := if p 159 then d383 p else d381 p
theorem agree384 (p q : Pattern) (h : Agree support p q) : d384 p = d384 q := by
  simp only [d384, h 159 (by decide), agree383 p q h, agree381 p q h]
theorem nonnegative384 (p : Pattern) : 0 ≤ d384 p :=
  nonnegative_ite (p 159) (nonnegative383 p) (nonnegative381 p)
def d385 (p : Pattern) : Int := if p 158 then d384 p else d381 p
theorem agree385 (p q : Pattern) (h : Agree support p q) : d385 p = d385 q := by
  simp only [d385, h 158 (by decide), agree384 p q h, agree381 p q h]
theorem nonnegative385 (p : Pattern) : 0 ≤ d385 p :=
  nonnegative_ite (p 158) (nonnegative384 p) (nonnegative381 p)
def d386 (p : Pattern) : Int := if p 168 then d264 p else d55 p
theorem agree386 (p q : Pattern) (h : Agree support p q) : d386 p = d386 q := by
  simp only [d386, h 168 (by decide), agree264 p q h, agree55 p q h]
theorem nonnegative386 (p : Pattern) : 0 ≤ d386 p :=
  nonnegative_ite (p 168) (nonnegative264 p) (nonnegative55 p)
def d387 (p : Pattern) : Int := if p 160 then d386 p else d22 p
theorem agree387 (p q : Pattern) (h : Agree support p q) : d387 p = d387 q := by
  simp only [d387, h 160 (by decide), agree386 p q h, agree22 p q h]
theorem nonnegative387 (p : Pattern) : 0 ≤ d387 p :=
  nonnegative_ite (p 160) (nonnegative386 p) (nonnegative22 p)
def d388 (p : Pattern) : Int := if p 168 then d274 p else d120 p
theorem agree388 (p q : Pattern) (h : Agree support p q) : d388 p = d388 q := by
  simp only [d388, h 168 (by decide), agree274 p q h, agree120 p q h]
theorem nonnegative388 (p : Pattern) : 0 ≤ d388 p :=
  nonnegative_ite (p 168) (nonnegative274 p) (nonnegative120 p)
def d389 (p : Pattern) : Int := if p 160 then d386 p else d388 p
theorem agree389 (p q : Pattern) (h : Agree support p q) : d389 p = d389 q := by
  simp only [d389, h 160 (by decide), agree386 p q h, agree388 p q h]
theorem nonnegative389 (p : Pattern) : 0 ≤ d389 p :=
  nonnegative_ite (p 160) (nonnegative386 p) (nonnegative388 p)
def d390 (p : Pattern) : Int := if p 159 then d389 p else d387 p
theorem agree390 (p q : Pattern) (h : Agree support p q) : d390 p = d390 q := by
  simp only [d390, h 159 (by decide), agree389 p q h, agree387 p q h]
theorem nonnegative390 (p : Pattern) : 0 ≤ d390 p :=
  nonnegative_ite (p 159) (nonnegative389 p) (nonnegative387 p)
def d391 (p : Pattern) : Int := if p 158 then d390 p else d387 p
theorem agree391 (p q : Pattern) (h : Agree support p q) : d391 p = d391 q := by
  simp only [d391, h 158 (by decide), agree390 p q h, agree387 p q h]
theorem nonnegative391 (p : Pattern) : 0 ≤ d391 p :=
  nonnegative_ite (p 158) (nonnegative390 p) (nonnegative387 p)
def d392 (p : Pattern) : Int := if p 141 then d391 p else d385 p
theorem agree392 (p q : Pattern) (h : Agree support p q) : d392 p = d392 q := by
  simp only [d392, h 141 (by decide), agree391 p q h, agree385 p q h]
theorem nonnegative392 (p : Pattern) : 0 ≤ d392 p :=
  nonnegative_ite (p 141) (nonnegative391 p) (nonnegative385 p)
def d393 (p : Pattern) : Int := if p 134 then d392 p else d379 p
theorem agree393 (p q : Pattern) (h : Agree support p q) : d393 p = d393 q := by
  simp only [d393, h 134 (by decide), agree392 p q h, agree379 p q h]
theorem nonnegative393 (p : Pattern) : 0 ≤ d393 p :=
  nonnegative_ite (p 134) (nonnegative392 p) (nonnegative379 p)
def d394 (p : Pattern) : Int := if p 158 then d380 p else d376 p
theorem agree394 (p q : Pattern) (h : Agree support p q) : d394 p = d394 q := by
  simp only [d394, h 158 (by decide), agree380 p q h, agree376 p q h]
theorem nonnegative394 (p : Pattern) : 0 ≤ d394 p :=
  nonnegative_ite (p 158) (nonnegative380 p) (nonnegative376 p)
def d395 (p : Pattern) : Int := if p 158 then d386 p else d378 p
theorem agree395 (p q : Pattern) (h : Agree support p q) : d395 p = d395 q := by
  simp only [d395, h 158 (by decide), agree386 p q h, agree378 p q h]
theorem nonnegative395 (p : Pattern) : 0 ≤ d395 p :=
  nonnegative_ite (p 158) (nonnegative386 p) (nonnegative378 p)
def d396 (p : Pattern) : Int := if p 141 then d395 p else d394 p
theorem agree396 (p q : Pattern) (h : Agree support p q) : d396 p = d396 q := by
  simp only [d396, h 141 (by decide), agree395 p q h, agree394 p q h]
theorem nonnegative396 (p : Pattern) : 0 ≤ d396 p :=
  nonnegative_ite (p 141) (nonnegative395 p) (nonnegative394 p)
def d397 (p : Pattern) : Int := if p 158 then d380 p else d384 p
theorem agree397 (p q : Pattern) (h : Agree support p q) : d397 p = d397 q := by
  simp only [d397, h 158 (by decide), agree380 p q h, agree384 p q h]
theorem nonnegative397 (p : Pattern) : 0 ≤ d397 p :=
  nonnegative_ite (p 158) (nonnegative380 p) (nonnegative384 p)
def d398 (p : Pattern) : Int := if p 158 then d386 p else d390 p
theorem agree398 (p q : Pattern) (h : Agree support p q) : d398 p = d398 q := by
  simp only [d398, h 158 (by decide), agree386 p q h, agree390 p q h]
theorem nonnegative398 (p : Pattern) : 0 ≤ d398 p :=
  nonnegative_ite (p 158) (nonnegative386 p) (nonnegative390 p)
def d399 (p : Pattern) : Int := if p 141 then d398 p else d397 p
theorem agree399 (p q : Pattern) (h : Agree support p q) : d399 p = d399 q := by
  simp only [d399, h 141 (by decide), agree398 p q h, agree397 p q h]
theorem nonnegative399 (p : Pattern) : 0 ≤ d399 p :=
  nonnegative_ite (p 141) (nonnegative398 p) (nonnegative397 p)
def d400 (p : Pattern) : Int := if p 134 then d399 p else d396 p
theorem agree400 (p q : Pattern) (h : Agree support p q) : d400 p = d400 q := by
  simp only [d400, h 134 (by decide), agree399 p q h, agree396 p q h]
theorem nonnegative400 (p : Pattern) : 0 ≤ d400 p :=
  nonnegative_ite (p 134) (nonnegative399 p) (nonnegative396 p)
def d401 (p : Pattern) : Int := if p 133 then d400 p else d393 p
theorem agree401 (p q : Pattern) (h : Agree support p q) : d401 p = d401 q := by
  simp only [d401, h 133 (by decide), agree400 p q h, agree393 p q h]
theorem nonnegative401 (p : Pattern) : 0 ≤ d401 p :=
  nonnegative_ite (p 133) (nonnegative400 p) (nonnegative393 p)
def d402 (p : Pattern) : Int := if p 141 then d386 p else d380 p
theorem agree402 (p q : Pattern) (h : Agree support p q) : d402 p = d402 q := by
  simp only [d402, h 141 (by decide), agree386 p q h, agree380 p q h]
theorem nonnegative402 (p : Pattern) : 0 ≤ d402 p :=
  nonnegative_ite (p 141) (nonnegative386 p) (nonnegative380 p)
def d403 (p : Pattern) : Int := if p 133 then d402 p else d400 p
theorem agree403 (p q : Pattern) (h : Agree support p q) : d403 p = d403 q := by
  simp only [d403, h 133 (by decide), agree402 p q h, agree400 p q h]
theorem nonnegative403 (p : Pattern) : 0 ≤ d403 p :=
  nonnegative_ite (p 133) (nonnegative402 p) (nonnegative400 p)
def d404 (p : Pattern) : Int := if p 132 then d403 p else d401 p
theorem agree404 (p q : Pattern) (h : Agree support p q) : d404 p = d404 q := by
  simp only [d404, h 132 (by decide), agree403 p q h, agree401 p q h]
theorem nonnegative404 (p : Pattern) : 0 ≤ d404 p :=
  nonnegative_ite (p 132) (nonnegative403 p) (nonnegative401 p)
def d405 (p : Pattern) : Int := if p 168 then d290 p else d137 p
theorem agree405 (p q : Pattern) (h : Agree support p q) : d405 p = d405 q := by
  simp only [d405, h 168 (by decide), agree290 p q h, agree137 p q h]
theorem nonnegative405 (p : Pattern) : 0 ≤ d405 p :=
  nonnegative_ite (p 168) (nonnegative290 p) (nonnegative137 p)
def d406 (p : Pattern) : Int := if p 160 then d405 p else d382 p
theorem agree406 (p q : Pattern) (h : Agree support p q) : d406 p = d406 q := by
  simp only [d406, h 160 (by decide), agree405 p q h, agree382 p q h]
theorem nonnegative406 (p : Pattern) : 0 ≤ d406 p :=
  nonnegative_ite (p 160) (nonnegative405 p) (nonnegative382 p)
def d407 (p : Pattern) : Int := if p 159 then d406 p else d376 p
theorem agree407 (p q : Pattern) (h : Agree support p q) : d407 p = d407 q := by
  simp only [d407, h 159 (by decide), agree406 p q h, agree376 p q h]
theorem nonnegative407 (p : Pattern) : 0 ≤ d407 p :=
  nonnegative_ite (p 159) (nonnegative406 p) (nonnegative376 p)
def d408 (p : Pattern) : Int := if p 158 then d407 p else d376 p
theorem agree408 (p q : Pattern) (h : Agree support p q) : d408 p = d408 q := by
  simp only [d408, h 158 (by decide), agree407 p q h, agree376 p q h]
theorem nonnegative408 (p : Pattern) : 0 ≤ d408 p :=
  nonnegative_ite (p 158) (nonnegative407 p) (nonnegative376 p)
def d409 (p : Pattern) : Int := if p 168 then d291 p else d137 p
theorem agree409 (p q : Pattern) (h : Agree support p q) : d409 p = d409 q := by
  simp only [d409, h 168 (by decide), agree291 p q h, agree137 p q h]
theorem nonnegative409 (p : Pattern) : 0 ≤ d409 p :=
  nonnegative_ite (p 168) (nonnegative291 p) (nonnegative137 p)
def d410 (p : Pattern) : Int := if p 160 then d409 p else d388 p
theorem agree410 (p q : Pattern) (h : Agree support p q) : d410 p = d410 q := by
  simp only [d410, h 160 (by decide), agree409 p q h, agree388 p q h]
theorem nonnegative410 (p : Pattern) : 0 ≤ d410 p :=
  nonnegative_ite (p 160) (nonnegative409 p) (nonnegative388 p)
def d411 (p : Pattern) : Int := if p 159 then d410 p else d378 p
theorem agree411 (p q : Pattern) (h : Agree support p q) : d411 p = d411 q := by
  simp only [d411, h 159 (by decide), agree410 p q h, agree378 p q h]
theorem nonnegative411 (p : Pattern) : 0 ≤ d411 p :=
  nonnegative_ite (p 159) (nonnegative410 p) (nonnegative378 p)
def d412 (p : Pattern) : Int := if p 158 then d411 p else d378 p
theorem agree412 (p q : Pattern) (h : Agree support p q) : d412 p = d412 q := by
  simp only [d412, h 158 (by decide), agree411 p q h, agree378 p q h]
theorem nonnegative412 (p : Pattern) : 0 ≤ d412 p :=
  nonnegative_ite (p 158) (nonnegative411 p) (nonnegative378 p)
def d413 (p : Pattern) : Int := if p 141 then d412 p else d408 p
theorem agree413 (p q : Pattern) (h : Agree support p q) : d413 p = d413 q := by
  simp only [d413, h 141 (by decide), agree412 p q h, agree408 p q h]
theorem nonnegative413 (p : Pattern) : 0 ≤ d413 p :=
  nonnegative_ite (p 141) (nonnegative412 p) (nonnegative408 p)
def d414 (p : Pattern) : Int := if p 134 then d402 p else d413 p
theorem agree414 (p q : Pattern) (h : Agree support p q) : d414 p = d414 q := by
  simp only [d414, h 134 (by decide), agree402 p q h, agree413 p q h]
theorem nonnegative414 (p : Pattern) : 0 ≤ d414 p :=
  nonnegative_ite (p 134) (nonnegative402 p) (nonnegative413 p)
def d415 (p : Pattern) : Int := if p 160 then d405 p else d21 p
theorem agree415 (p q : Pattern) (h : Agree support p q) : d415 p = d415 q := by
  simp only [d415, h 160 (by decide), agree405 p q h, agree21 p q h]
theorem nonnegative415 (p : Pattern) : 0 ≤ d415 p :=
  nonnegative_ite (p 160) (nonnegative405 p) (nonnegative21 p)
def d416 (p : Pattern) : Int := if p 159 then d406 p else d415 p
theorem agree416 (p q : Pattern) (h : Agree support p q) : d416 p = d416 q := by
  simp only [d416, h 159 (by decide), agree406 p q h, agree415 p q h]
theorem nonnegative416 (p : Pattern) : 0 ≤ d416 p :=
  nonnegative_ite (p 159) (nonnegative406 p) (nonnegative415 p)
def d417 (p : Pattern) : Int := if p 158 then d380 p else d416 p
theorem agree417 (p q : Pattern) (h : Agree support p q) : d417 p = d417 q := by
  simp only [d417, h 158 (by decide), agree380 p q h, agree416 p q h]
theorem nonnegative417 (p : Pattern) : 0 ≤ d417 p :=
  nonnegative_ite (p 158) (nonnegative380 p) (nonnegative416 p)
def d418 (p : Pattern) : Int := if p 160 then d409 p else d22 p
theorem agree418 (p q : Pattern) (h : Agree support p q) : d418 p = d418 q := by
  simp only [d418, h 160 (by decide), agree409 p q h, agree22 p q h]
theorem nonnegative418 (p : Pattern) : 0 ≤ d418 p :=
  nonnegative_ite (p 160) (nonnegative409 p) (nonnegative22 p)
def d419 (p : Pattern) : Int := if p 159 then d410 p else d418 p
theorem agree419 (p q : Pattern) (h : Agree support p q) : d419 p = d419 q := by
  simp only [d419, h 159 (by decide), agree410 p q h, agree418 p q h]
theorem nonnegative419 (p : Pattern) : 0 ≤ d419 p :=
  nonnegative_ite (p 159) (nonnegative410 p) (nonnegative418 p)
def d420 (p : Pattern) : Int := if p 158 then d386 p else d419 p
theorem agree420 (p q : Pattern) (h : Agree support p q) : d420 p = d420 q := by
  simp only [d420, h 158 (by decide), agree386 p q h, agree419 p q h]
theorem nonnegative420 (p : Pattern) : 0 ≤ d420 p :=
  nonnegative_ite (p 158) (nonnegative386 p) (nonnegative419 p)
def d421 (p : Pattern) : Int := if p 141 then d420 p else d417 p
theorem agree421 (p q : Pattern) (h : Agree support p q) : d421 p = d421 q := by
  simp only [d421, h 141 (by decide), agree420 p q h, agree417 p q h]
theorem nonnegative421 (p : Pattern) : 0 ≤ d421 p :=
  nonnegative_ite (p 141) (nonnegative420 p) (nonnegative417 p)
def d422 (p : Pattern) : Int := if p 134 then d402 p else d421 p
theorem agree422 (p q : Pattern) (h : Agree support p q) : d422 p = d422 q := by
  simp only [d422, h 134 (by decide), agree402 p q h, agree421 p q h]
theorem nonnegative422 (p : Pattern) : 0 ≤ d422 p :=
  nonnegative_ite (p 134) (nonnegative402 p) (nonnegative421 p)
def d423 (p : Pattern) : Int := if p 133 then d422 p else d414 p
theorem agree423 (p q : Pattern) (h : Agree support p q) : d423 p = d423 q := by
  simp only [d423, h 133 (by decide), agree422 p q h, agree414 p q h]
theorem nonnegative423 (p : Pattern) : 0 ≤ d423 p :=
  nonnegative_ite (p 133) (nonnegative422 p) (nonnegative414 p)
def d424 (p : Pattern) : Int := if p 158 then d380 p else d407 p
theorem agree424 (p q : Pattern) (h : Agree support p q) : d424 p = d424 q := by
  simp only [d424, h 158 (by decide), agree380 p q h, agree407 p q h]
theorem nonnegative424 (p : Pattern) : 0 ≤ d424 p :=
  nonnegative_ite (p 158) (nonnegative380 p) (nonnegative407 p)
def d425 (p : Pattern) : Int := if p 158 then d386 p else d411 p
theorem agree425 (p q : Pattern) (h : Agree support p q) : d425 p = d425 q := by
  simp only [d425, h 158 (by decide), agree386 p q h, agree411 p q h]
theorem nonnegative425 (p : Pattern) : 0 ≤ d425 p :=
  nonnegative_ite (p 158) (nonnegative386 p) (nonnegative411 p)
def d426 (p : Pattern) : Int := if p 141 then d425 p else d424 p
theorem agree426 (p q : Pattern) (h : Agree support p q) : d426 p = d426 q := by
  simp only [d426, h 141 (by decide), agree425 p q h, agree424 p q h]
theorem nonnegative426 (p : Pattern) : 0 ≤ d426 p :=
  nonnegative_ite (p 141) (nonnegative425 p) (nonnegative424 p)
def d427 (p : Pattern) : Int := if p 134 then d402 p else d426 p
theorem agree427 (p q : Pattern) (h : Agree support p q) : d427 p = d427 q := by
  simp only [d427, h 134 (by decide), agree402 p q h, agree426 p q h]
theorem nonnegative427 (p : Pattern) : 0 ≤ d427 p :=
  nonnegative_ite (p 134) (nonnegative402 p) (nonnegative426 p)
def d428 (p : Pattern) : Int := if p 133 then d402 p else d427 p
theorem agree428 (p q : Pattern) (h : Agree support p q) : d428 p = d428 q := by
  simp only [d428, h 133 (by decide), agree402 p q h, agree427 p q h]
theorem nonnegative428 (p : Pattern) : 0 ≤ d428 p :=
  nonnegative_ite (p 133) (nonnegative402 p) (nonnegative427 p)
def d429 (p : Pattern) : Int := if p 132 then d428 p else d423 p
theorem agree429 (p q : Pattern) (h : Agree support p q) : d429 p = d429 q := by
  simp only [d429, h 132 (by decide), agree428 p q h, agree423 p q h]
theorem nonnegative429 (p : Pattern) : 0 ≤ d429 p :=
  nonnegative_ite (p 132) (nonnegative428 p) (nonnegative423 p)
def d430 (p : Pattern) : Int := if p 108 then d429 p else d404 p
theorem agree430 (p q : Pattern) (h : Agree support p q) : d430 p = d430 q := by
  simp only [d430, h 108 (by decide), agree429 p q h, agree404 p q h]
theorem nonnegative430 (p : Pattern) : 0 ≤ d430 p :=
  nonnegative_ite (p 108) (nonnegative429 p) (nonnegative404 p)
def d431 (p : Pattern) : Int := if p 160 then d2 p else d45 p
theorem agree431 (p q : Pattern) (h : Agree support p q) : d431 p = d431 q := by
  simp only [d431, h 160 (by decide), agree2 p q h, agree45 p q h]
theorem nonnegative431 (p : Pattern) : 0 ≤ d431 p :=
  nonnegative_ite (p 160) (nonnegative2 p) (nonnegative45 p)
def d432 (p : Pattern) : Int := if p 134 then d431 p else d45 p
theorem agree432 (p q : Pattern) (h : Agree support p q) : d432 p = d432 q := by
  simp only [d432, h 134 (by decide), agree431 p q h, agree45 p q h]
theorem nonnegative432 (p : Pattern) : 0 ≤ d432 p :=
  nonnegative_ite (p 134) (nonnegative431 p) (nonnegative45 p)
def d433 (p : Pattern) : Int := if p 158 then d2 p else d45 p
theorem agree433 (p q : Pattern) (h : Agree support p q) : d433 p = d433 q := by
  simp only [d433, h 158 (by decide), agree2 p q h, agree45 p q h]
theorem nonnegative433 (p : Pattern) : 0 ≤ d433 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative45 p)
def d434 (p : Pattern) : Int := if p 158 then d2 p else d431 p
theorem agree434 (p q : Pattern) (h : Agree support p q) : d434 p = d434 q := by
  simp only [d434, h 158 (by decide), agree2 p q h, agree431 p q h]
theorem nonnegative434 (p : Pattern) : 0 ≤ d434 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative431 p)
def d435 (p : Pattern) : Int := if p 134 then d434 p else d433 p
theorem agree435 (p q : Pattern) (h : Agree support p q) : d435 p = d435 q := by
  simp only [d435, h 134 (by decide), agree434 p q h, agree433 p q h]
theorem nonnegative435 (p : Pattern) : 0 ≤ d435 p :=
  nonnegative_ite (p 134) (nonnegative434 p) (nonnegative433 p)
def d436 (p : Pattern) : Int := if p 133 then d435 p else d432 p
theorem agree436 (p q : Pattern) (h : Agree support p q) : d436 p = d436 q := by
  simp only [d436, h 133 (by decide), agree435 p q h, agree432 p q h]
theorem nonnegative436 (p : Pattern) : 0 ≤ d436 p :=
  nonnegative_ite (p 133) (nonnegative435 p) (nonnegative432 p)
def d437 (p : Pattern) : Int := if p 133 then d2 p else d435 p
theorem agree437 (p q : Pattern) (h : Agree support p q) : d437 p = d437 q := by
  simp only [d437, h 133 (by decide), agree2 p q h, agree435 p q h]
theorem nonnegative437 (p : Pattern) : 0 ≤ d437 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative435 p)
def d438 (p : Pattern) : Int := if p 132 then d437 p else d436 p
theorem agree438 (p q : Pattern) (h : Agree support p q) : d438 p = d438 q := by
  simp only [d438, h 132 (by decide), agree437 p q h, agree436 p q h]
theorem nonnegative438 (p : Pattern) : 0 ≤ d438 p :=
  nonnegative_ite (p 132) (nonnegative437 p) (nonnegative436 p)
def d439 (p : Pattern) : Int := if p 160 then d92 p else d45 p
theorem agree439 (p q : Pattern) (h : Agree support p q) : d439 p = d439 q := by
  simp only [d439, h 160 (by decide), agree92 p q h, agree45 p q h]
theorem nonnegative439 (p : Pattern) : 0 ≤ d439 p :=
  nonnegative_ite (p 160) (nonnegative92 p) (nonnegative45 p)
def d440 (p : Pattern) : Int := if p 159 then d439 p else d45 p
theorem agree440 (p q : Pattern) (h : Agree support p q) : d440 p = d440 q := by
  simp only [d440, h 159 (by decide), agree439 p q h, agree45 p q h]
theorem nonnegative440 (p : Pattern) : 0 ≤ d440 p :=
  nonnegative_ite (p 159) (nonnegative439 p) (nonnegative45 p)
def d441 (p : Pattern) : Int := if p 158 then d440 p else d45 p
theorem agree441 (p q : Pattern) (h : Agree support p q) : d441 p = d441 q := by
  simp only [d441, h 158 (by decide), agree440 p q h, agree45 p q h]
theorem nonnegative441 (p : Pattern) : 0 ≤ d441 p :=
  nonnegative_ite (p 158) (nonnegative440 p) (nonnegative45 p)
def d442 (p : Pattern) : Int := if p 134 then d2 p else d441 p
theorem agree442 (p q : Pattern) (h : Agree support p q) : d442 p = d442 q := by
  simp only [d442, h 134 (by decide), agree2 p q h, agree441 p q h]
theorem nonnegative442 (p : Pattern) : 0 ≤ d442 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative441 p)
def d443 (p : Pattern) : Int := if p 158 then d2 p else d439 p
theorem agree443 (p q : Pattern) (h : Agree support p q) : d443 p = d443 q := by
  simp only [d443, h 158 (by decide), agree2 p q h, agree439 p q h]
theorem nonnegative443 (p : Pattern) : 0 ≤ d443 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative439 p)
def d444 (p : Pattern) : Int := if p 134 then d2 p else d443 p
theorem agree444 (p q : Pattern) (h : Agree support p q) : d444 p = d444 q := by
  simp only [d444, h 134 (by decide), agree2 p q h, agree443 p q h]
theorem nonnegative444 (p : Pattern) : 0 ≤ d444 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative443 p)
def d445 (p : Pattern) : Int := if p 133 then d444 p else d442 p
theorem agree445 (p q : Pattern) (h : Agree support p q) : d445 p = d445 q := by
  simp only [d445, h 133 (by decide), agree444 p q h, agree442 p q h]
theorem nonnegative445 (p : Pattern) : 0 ≤ d445 p :=
  nonnegative_ite (p 133) (nonnegative444 p) (nonnegative442 p)
def d446 (p : Pattern) : Int := if p 158 then d2 p else d440 p
theorem agree446 (p q : Pattern) (h : Agree support p q) : d446 p = d446 q := by
  simp only [d446, h 158 (by decide), agree2 p q h, agree440 p q h]
theorem nonnegative446 (p : Pattern) : 0 ≤ d446 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative440 p)
def d447 (p : Pattern) : Int := if p 134 then d2 p else d446 p
theorem agree447 (p q : Pattern) (h : Agree support p q) : d447 p = d447 q := by
  simp only [d447, h 134 (by decide), agree2 p q h, agree446 p q h]
theorem nonnegative447 (p : Pattern) : 0 ≤ d447 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative446 p)
def d448 (p : Pattern) : Int := if p 133 then d2 p else d447 p
theorem agree448 (p q : Pattern) (h : Agree support p q) : d448 p = d448 q := by
  simp only [d448, h 133 (by decide), agree2 p q h, agree447 p q h]
theorem nonnegative448 (p : Pattern) : 0 ≤ d448 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative447 p)
def d449 (p : Pattern) : Int := if p 132 then d448 p else d445 p
theorem agree449 (p q : Pattern) (h : Agree support p q) : d449 p = d449 q := by
  simp only [d449, h 132 (by decide), agree448 p q h, agree445 p q h]
theorem nonnegative449 (p : Pattern) : 0 ≤ d449 p :=
  nonnegative_ite (p 132) (nonnegative448 p) (nonnegative445 p)
def d450 (p : Pattern) : Int := if p 108 then d449 p else d438 p
theorem agree450 (p q : Pattern) (h : Agree support p q) : d450 p = d450 q := by
  simp only [d450, h 108 (by decide), agree449 p q h, agree438 p q h]
theorem nonnegative450 (p : Pattern) : 0 ≤ d450 p :=
  nonnegative_ite (p 108) (nonnegative449 p) (nonnegative438 p)
def d451 (p : Pattern) : Int := if p 141 then d62 p else d56 p
theorem agree451 (p q : Pattern) (h : Agree support p q) : d451 p = d451 q := by
  simp only [d451, h 141 (by decide), agree62 p q h, agree56 p q h]
theorem nonnegative451 (p : Pattern) : 0 ≤ d451 p :=
  nonnegative_ite (p 141) (nonnegative62 p) (nonnegative56 p)
def d452 (p : Pattern) : Int := if p 160 then d55 p else d56 p
theorem agree452 (p q : Pattern) (h : Agree support p q) : d452 p = d452 q := by
  simp only [d452, h 160 (by decide), agree55 p q h, agree56 p q h]
theorem nonnegative452 (p : Pattern) : 0 ≤ d452 p :=
  nonnegative_ite (p 160) (nonnegative55 p) (nonnegative56 p)
def d453 (p : Pattern) : Int := if p 160 then d65 p else d62 p
theorem agree453 (p q : Pattern) (h : Agree support p q) : d453 p = d453 q := by
  simp only [d453, h 160 (by decide), agree65 p q h, agree62 p q h]
theorem nonnegative453 (p : Pattern) : 0 ≤ d453 p :=
  nonnegative_ite (p 160) (nonnegative65 p) (nonnegative62 p)
def d454 (p : Pattern) : Int := if p 141 then d453 p else d452 p
theorem agree454 (p q : Pattern) (h : Agree support p q) : d454 p = d454 q := by
  simp only [d454, h 141 (by decide), agree453 p q h, agree452 p q h]
theorem nonnegative454 (p : Pattern) : 0 ≤ d454 p :=
  nonnegative_ite (p 141) (nonnegative453 p) (nonnegative452 p)
def d455 (p : Pattern) : Int := if p 134 then d454 p else d451 p
theorem agree455 (p q : Pattern) (h : Agree support p q) : d455 p = d455 q := by
  simp only [d455, h 134 (by decide), agree454 p q h, agree451 p q h]
theorem nonnegative455 (p : Pattern) : 0 ≤ d455 p :=
  nonnegative_ite (p 134) (nonnegative454 p) (nonnegative451 p)
def d456 (p : Pattern) : Int := if p 158 then d55 p else d56 p
theorem agree456 (p q : Pattern) (h : Agree support p q) : d456 p = d456 q := by
  simp only [d456, h 158 (by decide), agree55 p q h, agree56 p q h]
theorem nonnegative456 (p : Pattern) : 0 ≤ d456 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative56 p)
def d457 (p : Pattern) : Int := if p 158 then d65 p else d62 p
theorem agree457 (p q : Pattern) (h : Agree support p q) : d457 p = d457 q := by
  simp only [d457, h 158 (by decide), agree65 p q h, agree62 p q h]
theorem nonnegative457 (p : Pattern) : 0 ≤ d457 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative62 p)
def d458 (p : Pattern) : Int := if p 141 then d457 p else d456 p
theorem agree458 (p q : Pattern) (h : Agree support p q) : d458 p = d458 q := by
  simp only [d458, h 141 (by decide), agree457 p q h, agree456 p q h]
theorem nonnegative458 (p : Pattern) : 0 ≤ d458 p :=
  nonnegative_ite (p 141) (nonnegative457 p) (nonnegative456 p)
def d459 (p : Pattern) : Int := if p 158 then d55 p else d452 p
theorem agree459 (p q : Pattern) (h : Agree support p q) : d459 p = d459 q := by
  simp only [d459, h 158 (by decide), agree55 p q h, agree452 p q h]
theorem nonnegative459 (p : Pattern) : 0 ≤ d459 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative452 p)
def d460 (p : Pattern) : Int := if p 158 then d65 p else d453 p
theorem agree460 (p q : Pattern) (h : Agree support p q) : d460 p = d460 q := by
  simp only [d460, h 158 (by decide), agree65 p q h, agree453 p q h]
theorem nonnegative460 (p : Pattern) : 0 ≤ d460 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative453 p)
def d461 (p : Pattern) : Int := if p 141 then d460 p else d459 p
theorem agree461 (p q : Pattern) (h : Agree support p q) : d461 p = d461 q := by
  simp only [d461, h 141 (by decide), agree460 p q h, agree459 p q h]
theorem nonnegative461 (p : Pattern) : 0 ≤ d461 p :=
  nonnegative_ite (p 141) (nonnegative460 p) (nonnegative459 p)
def d462 (p : Pattern) : Int := if p 134 then d461 p else d458 p
theorem agree462 (p q : Pattern) (h : Agree support p q) : d462 p = d462 q := by
  simp only [d462, h 134 (by decide), agree461 p q h, agree458 p q h]
theorem nonnegative462 (p : Pattern) : 0 ≤ d462 p :=
  nonnegative_ite (p 134) (nonnegative461 p) (nonnegative458 p)
def d463 (p : Pattern) : Int := if p 133 then d462 p else d455 p
theorem agree463 (p q : Pattern) (h : Agree support p q) : d463 p = d463 q := by
  simp only [d463, h 133 (by decide), agree462 p q h, agree455 p q h]
theorem nonnegative463 (p : Pattern) : 0 ≤ d463 p :=
  nonnegative_ite (p 133) (nonnegative462 p) (nonnegative455 p)
def d464 (p : Pattern) : Int := if p 133 then d66 p else d462 p
theorem agree464 (p q : Pattern) (h : Agree support p q) : d464 p = d464 q := by
  simp only [d464, h 133 (by decide), agree66 p q h, agree462 p q h]
theorem nonnegative464 (p : Pattern) : 0 ≤ d464 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative462 p)
def d465 (p : Pattern) : Int := if p 132 then d464 p else d463 p
theorem agree465 (p q : Pattern) (h : Agree support p q) : d465 p = d465 q := by
  simp only [d465, h 132 (by decide), agree464 p q h, agree463 p q h]
theorem nonnegative465 (p : Pattern) : 0 ≤ d465 p :=
  nonnegative_ite (p 132) (nonnegative464 p) (nonnegative463 p)
def d466 (p : Pattern) : Int := if p 160 then d137 p else d56 p
theorem agree466 (p q : Pattern) (h : Agree support p q) : d466 p = d466 q := by
  simp only [d466, h 160 (by decide), agree137 p q h, agree56 p q h]
theorem nonnegative466 (p : Pattern) : 0 ≤ d466 p :=
  nonnegative_ite (p 160) (nonnegative137 p) (nonnegative56 p)
def d467 (p : Pattern) : Int := if p 159 then d466 p else d56 p
theorem agree467 (p q : Pattern) (h : Agree support p q) : d467 p = d467 q := by
  simp only [d467, h 159 (by decide), agree466 p q h, agree56 p q h]
theorem nonnegative467 (p : Pattern) : 0 ≤ d467 p :=
  nonnegative_ite (p 159) (nonnegative466 p) (nonnegative56 p)
def d468 (p : Pattern) : Int := if p 158 then d467 p else d56 p
theorem agree468 (p q : Pattern) (h : Agree support p q) : d468 p = d468 q := by
  simp only [d468, h 158 (by decide), agree467 p q h, agree56 p q h]
theorem nonnegative468 (p : Pattern) : 0 ≤ d468 p :=
  nonnegative_ite (p 158) (nonnegative467 p) (nonnegative56 p)
def d469 (p : Pattern) : Int := if p 160 then d144 p else d62 p
theorem agree469 (p q : Pattern) (h : Agree support p q) : d469 p = d469 q := by
  simp only [d469, h 160 (by decide), agree144 p q h, agree62 p q h]
theorem nonnegative469 (p : Pattern) : 0 ≤ d469 p :=
  nonnegative_ite (p 160) (nonnegative144 p) (nonnegative62 p)
def d470 (p : Pattern) : Int := if p 159 then d469 p else d62 p
theorem agree470 (p q : Pattern) (h : Agree support p q) : d470 p = d470 q := by
  simp only [d470, h 159 (by decide), agree469 p q h, agree62 p q h]
theorem nonnegative470 (p : Pattern) : 0 ≤ d470 p :=
  nonnegative_ite (p 159) (nonnegative469 p) (nonnegative62 p)
def d471 (p : Pattern) : Int := if p 158 then d470 p else d62 p
theorem agree471 (p q : Pattern) (h : Agree support p q) : d471 p = d471 q := by
  simp only [d471, h 158 (by decide), agree470 p q h, agree62 p q h]
theorem nonnegative471 (p : Pattern) : 0 ≤ d471 p :=
  nonnegative_ite (p 158) (nonnegative470 p) (nonnegative62 p)
def d472 (p : Pattern) : Int := if p 141 then d471 p else d468 p
theorem agree472 (p q : Pattern) (h : Agree support p q) : d472 p = d472 q := by
  simp only [d472, h 141 (by decide), agree471 p q h, agree468 p q h]
theorem nonnegative472 (p : Pattern) : 0 ≤ d472 p :=
  nonnegative_ite (p 141) (nonnegative471 p) (nonnegative468 p)
def d473 (p : Pattern) : Int := if p 134 then d66 p else d472 p
theorem agree473 (p q : Pattern) (h : Agree support p q) : d473 p = d473 q := by
  simp only [d473, h 134 (by decide), agree66 p q h, agree472 p q h]
theorem nonnegative473 (p : Pattern) : 0 ≤ d473 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative472 p)
def d474 (p : Pattern) : Int := if p 158 then d55 p else d466 p
theorem agree474 (p q : Pattern) (h : Agree support p q) : d474 p = d474 q := by
  simp only [d474, h 158 (by decide), agree55 p q h, agree466 p q h]
theorem nonnegative474 (p : Pattern) : 0 ≤ d474 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative466 p)
def d475 (p : Pattern) : Int := if p 158 then d65 p else d469 p
theorem agree475 (p q : Pattern) (h : Agree support p q) : d475 p = d475 q := by
  simp only [d475, h 158 (by decide), agree65 p q h, agree469 p q h]
theorem nonnegative475 (p : Pattern) : 0 ≤ d475 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative469 p)
def d476 (p : Pattern) : Int := if p 141 then d475 p else d474 p
theorem agree476 (p q : Pattern) (h : Agree support p q) : d476 p = d476 q := by
  simp only [d476, h 141 (by decide), agree475 p q h, agree474 p q h]
theorem nonnegative476 (p : Pattern) : 0 ≤ d476 p :=
  nonnegative_ite (p 141) (nonnegative475 p) (nonnegative474 p)
def d477 (p : Pattern) : Int := if p 134 then d66 p else d476 p
theorem agree477 (p q : Pattern) (h : Agree support p q) : d477 p = d477 q := by
  simp only [d477, h 134 (by decide), agree66 p q h, agree476 p q h]
theorem nonnegative477 (p : Pattern) : 0 ≤ d477 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative476 p)
def d478 (p : Pattern) : Int := if p 133 then d477 p else d473 p
theorem agree478 (p q : Pattern) (h : Agree support p q) : d478 p = d478 q := by
  simp only [d478, h 133 (by decide), agree477 p q h, agree473 p q h]
theorem nonnegative478 (p : Pattern) : 0 ≤ d478 p :=
  nonnegative_ite (p 133) (nonnegative477 p) (nonnegative473 p)
def d479 (p : Pattern) : Int := if p 158 then d55 p else d467 p
theorem agree479 (p q : Pattern) (h : Agree support p q) : d479 p = d479 q := by
  simp only [d479, h 158 (by decide), agree55 p q h, agree467 p q h]
theorem nonnegative479 (p : Pattern) : 0 ≤ d479 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative467 p)
end NetHack.Sokoban12CostPartition
