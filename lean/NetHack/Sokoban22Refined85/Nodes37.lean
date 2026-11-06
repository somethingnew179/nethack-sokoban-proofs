/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes36
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d4440 (p : Pattern) : Int := if p 141 then d137 p else d113 p
theorem agree4440 (p q : Pattern) (h : Agree support p q) : d4440 p = d4440 q := by
  simp only [d4440, h 141 (by decide), agree137 p q h, agree113 p q h]
theorem nonnegative4440 (p : Pattern) : 0 ≤ d4440 p :=
  nonnegative_ite (p 141) (nonnegative137 p) (nonnegative113 p)
def d4441 (p : Pattern) : Int := if p 138 then d12 p else d4440 p
theorem agree4441 (p q : Pattern) (h : Agree support p q) : d4441 p = d4441 q := by
  simp only [d4441, h 138 (by decide), agree12 p q h, agree4440 p q h]
theorem nonnegative4441 (p : Pattern) : 0 ≤ d4441 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4440 p)
def d4442 (p : Pattern) : Int := if p 116 then d4441 p else d4440 p
theorem agree4442 (p q : Pattern) (h : Agree support p q) : d4442 p = d4442 q := by
  simp only [d4442, h 116 (by decide), agree4441 p q h, agree4440 p q h]
theorem nonnegative4442 (p : Pattern) : 0 ≤ d4442 p :=
  nonnegative_ite (p 116) (nonnegative4441 p) (nonnegative4440 p)
def d4443 (p : Pattern) : Int := if p 71 then d4442 p else d4439 p
theorem agree4443 (p q : Pattern) (h : Agree support p q) : d4443 p = d4443 q := by
  simp only [d4443, h 71 (by decide), agree4442 p q h, agree4439 p q h]
theorem nonnegative4443 (p : Pattern) : 0 ≤ d4443 p :=
  nonnegative_ite (p 71) (nonnegative4442 p) (nonnegative4439 p)
def d4444 (p : Pattern) : Int := if p 49 then d4443 p else d4439 p
theorem agree4444 (p q : Pattern) (h : Agree support p q) : d4444 p = d4444 q := by
  simp only [d4444, h 49 (by decide), agree4443 p q h, agree4439 p q h]
theorem nonnegative4444 (p : Pattern) : 0 ≤ d4444 p :=
  nonnegative_ite (p 49) (nonnegative4443 p) (nonnegative4439 p)
def d4445 (p : Pattern) : Int := if p 141 then d84 p else d80 p
theorem agree4445 (p q : Pattern) (h : Agree support p q) : d4445 p = d4445 q := by
  simp only [d4445, h 141 (by decide), agree84 p q h, agree80 p q h]
theorem nonnegative4445 (p : Pattern) : 0 ≤ d4445 p :=
  nonnegative_ite (p 141) (nonnegative84 p) (nonnegative80 p)
def d4446 (p : Pattern) : Int := if p 138 then d4445 p else d4433 p
theorem agree4446 (p q : Pattern) (h : Agree support p q) : d4446 p = d4446 q := by
  simp only [d4446, h 138 (by decide), agree4445 p q h, agree4433 p q h]
theorem nonnegative4446 (p : Pattern) : 0 ≤ d4446 p :=
  nonnegative_ite (p 138) (nonnegative4445 p) (nonnegative4433 p)
def d4447 (p : Pattern) : Int := if p 138 then d12 p else d4445 p
theorem agree4447 (p q : Pattern) (h : Agree support p q) : d4447 p = d4447 q := by
  simp only [d4447, h 138 (by decide), agree12 p q h, agree4445 p q h]
theorem nonnegative4447 (p : Pattern) : 0 ≤ d4447 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4445 p)
def d4448 (p : Pattern) : Int := if p 116 then d4447 p else d4446 p
theorem agree4448 (p q : Pattern) (h : Agree support p q) : d4448 p = d4448 q := by
  simp only [d4448, h 116 (by decide), agree4447 p q h, agree4446 p q h]
theorem nonnegative4448 (p : Pattern) : 0 ≤ d4448 p :=
  nonnegative_ite (p 116) (nonnegative4447 p) (nonnegative4446 p)
def d4449 (p : Pattern) : Int := if p 115 then d4448 p else d4436 p
theorem agree4449 (p q : Pattern) (h : Agree support p q) : d4449 p = d4449 q := by
  simp only [d4449, h 115 (by decide), agree4448 p q h, agree4436 p q h]
theorem nonnegative4449 (p : Pattern) : 0 ≤ d4449 p :=
  nonnegative_ite (p 115) (nonnegative4448 p) (nonnegative4436 p)
def d4450 (p : Pattern) : Int := if p 71 then d4449 p else d4439 p
theorem agree4450 (p q : Pattern) (h : Agree support p q) : d4450 p = d4450 q := by
  simp only [d4450, h 71 (by decide), agree4449 p q h, agree4439 p q h]
theorem nonnegative4450 (p : Pattern) : 0 ≤ d4450 p :=
  nonnegative_ite (p 71) (nonnegative4449 p) (nonnegative4439 p)
def d4451 (p : Pattern) : Int := if p 141 then d213 p else d113 p
theorem agree4451 (p q : Pattern) (h : Agree support p q) : d4451 p = d4451 q := by
  simp only [d4451, h 141 (by decide), agree213 p q h, agree113 p q h]
theorem nonnegative4451 (p : Pattern) : 0 ≤ d4451 p :=
  nonnegative_ite (p 141) (nonnegative213 p) (nonnegative113 p)
def d4452 (p : Pattern) : Int := if p 138 then d12 p else d4451 p
theorem agree4452 (p q : Pattern) (h : Agree support p q) : d4452 p = d4452 q := by
  simp only [d4452, h 138 (by decide), agree12 p q h, agree4451 p q h]
theorem nonnegative4452 (p : Pattern) : 0 ≤ d4452 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4451 p)
def d4453 (p : Pattern) : Int := if p 116 then d4452 p else d4451 p
theorem agree4453 (p q : Pattern) (h : Agree support p q) : d4453 p = d4453 q := by
  simp only [d4453, h 116 (by decide), agree4452 p q h, agree4451 p q h]
theorem nonnegative4453 (p : Pattern) : 0 ≤ d4453 p :=
  nonnegative_ite (p 116) (nonnegative4452 p) (nonnegative4451 p)
def d4454 (p : Pattern) : Int := if p 141 then d154 p else d137 p
theorem agree4454 (p q : Pattern) (h : Agree support p q) : d4454 p = d4454 q := by
  simp only [d4454, h 141 (by decide), agree154 p q h, agree137 p q h]
theorem nonnegative4454 (p : Pattern) : 0 ≤ d4454 p :=
  nonnegative_ite (p 141) (nonnegative154 p) (nonnegative137 p)
def d4455 (p : Pattern) : Int := if p 138 then d4454 p else d4451 p
theorem agree4455 (p q : Pattern) (h : Agree support p q) : d4455 p = d4455 q := by
  simp only [d4455, h 138 (by decide), agree4454 p q h, agree4451 p q h]
theorem nonnegative4455 (p : Pattern) : 0 ≤ d4455 p :=
  nonnegative_ite (p 138) (nonnegative4454 p) (nonnegative4451 p)
def d4456 (p : Pattern) : Int := if p 141 then d154 p else d255 p
theorem agree4456 (p q : Pattern) (h : Agree support p q) : d4456 p = d4456 q := by
  simp only [d4456, h 141 (by decide), agree154 p q h, agree255 p q h]
theorem nonnegative4456 (p : Pattern) : 0 ≤ d4456 p :=
  nonnegative_ite (p 141) (nonnegative154 p) (nonnegative255 p)
def d4457 (p : Pattern) : Int := if p 138 then d12 p else d4456 p
theorem agree4457 (p q : Pattern) (h : Agree support p q) : d4457 p = d4457 q := by
  simp only [d4457, h 138 (by decide), agree12 p q h, agree4456 p q h]
theorem nonnegative4457 (p : Pattern) : 0 ≤ d4457 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4456 p)
def d4458 (p : Pattern) : Int := if p 116 then d4457 p else d4455 p
theorem agree4458 (p q : Pattern) (h : Agree support p q) : d4458 p = d4458 q := by
  simp only [d4458, h 116 (by decide), agree4457 p q h, agree4455 p q h]
theorem nonnegative4458 (p : Pattern) : 0 ≤ d4458 p :=
  nonnegative_ite (p 116) (nonnegative4457 p) (nonnegative4455 p)
def d4459 (p : Pattern) : Int := if p 115 then d4458 p else d4453 p
theorem agree4459 (p q : Pattern) (h : Agree support p q) : d4459 p = d4459 q := by
  simp only [d4459, h 115 (by decide), agree4458 p q h, agree4453 p q h]
theorem nonnegative4459 (p : Pattern) : 0 ≤ d4459 p :=
  nonnegative_ite (p 115) (nonnegative4458 p) (nonnegative4453 p)
def d4460 (p : Pattern) : Int := if p 71 then d4459 p else d4439 p
theorem agree4460 (p q : Pattern) (h : Agree support p q) : d4460 p = d4460 q := by
  simp only [d4460, h 71 (by decide), agree4459 p q h, agree4439 p q h]
theorem nonnegative4460 (p : Pattern) : 0 ≤ d4460 p :=
  nonnegative_ite (p 71) (nonnegative4459 p) (nonnegative4439 p)
def d4461 (p : Pattern) : Int := if p 49 then d4460 p else d4450 p
theorem agree4461 (p q : Pattern) (h : Agree support p q) : d4461 p = d4461 q := by
  simp only [d4461, h 49 (by decide), agree4460 p q h, agree4450 p q h]
theorem nonnegative4461 (p : Pattern) : 0 ≤ d4461 p :=
  nonnegative_ite (p 49) (nonnegative4460 p) (nonnegative4450 p)
def d4462 (p : Pattern) : Int := if p 48 then d4461 p else d4444 p
theorem agree4462 (p q : Pattern) (h : Agree support p q) : d4462 p = d4462 q := by
  simp only [d4462, h 48 (by decide), agree4461 p q h, agree4444 p q h]
theorem nonnegative4462 (p : Pattern) : 0 ≤ d4462 p :=
  nonnegative_ite (p 48) (nonnegative4461 p) (nonnegative4444 p)
def d4463 (p : Pattern) : Int := if p 71 then d579 p else d543 p
theorem agree4463 (p q : Pattern) (h : Agree support p q) : d4463 p = d4463 q := by
  simp only [d4463, h 71 (by decide), agree579 p q h, agree543 p q h]
theorem nonnegative4463 (p : Pattern) : 0 ≤ d4463 p :=
  nonnegative_ite (p 71) (nonnegative579 p) (nonnegative543 p)
def d4464 (p : Pattern) : Int := if p 49 then d4463 p else d543 p
theorem agree4464 (p q : Pattern) (h : Agree support p q) : d4464 p = d4464 q := by
  simp only [d4464, h 49 (by decide), agree4463 p q h, agree543 p q h]
theorem nonnegative4464 (p : Pattern) : 0 ≤ d4464 p :=
  nonnegative_ite (p 49) (nonnegative4463 p) (nonnegative543 p)
def d4465 (p : Pattern) : Int := if p 115 then d605 p else d543 p
theorem agree4465 (p q : Pattern) (h : Agree support p q) : d4465 p = d4465 q := by
  simp only [d4465, h 115 (by decide), agree605 p q h, agree543 p q h]
theorem nonnegative4465 (p : Pattern) : 0 ≤ d4465 p :=
  nonnegative_ite (p 115) (nonnegative605 p) (nonnegative543 p)
def d4466 (p : Pattern) : Int := if p 71 then d4465 p else d543 p
theorem agree4466 (p q : Pattern) (h : Agree support p q) : d4466 p = d4466 q := by
  simp only [d4466, h 71 (by decide), agree4465 p q h, agree543 p q h]
theorem nonnegative4466 (p : Pattern) : 0 ≤ d4466 p :=
  nonnegative_ite (p 71) (nonnegative4465 p) (nonnegative543 p)
def d4467 (p : Pattern) : Int := if p 115 then d646 p else d616 p
theorem agree4467 (p q : Pattern) (h : Agree support p q) : d4467 p = d4467 q := by
  simp only [d4467, h 115 (by decide), agree646 p q h, agree616 p q h]
theorem nonnegative4467 (p : Pattern) : 0 ≤ d4467 p :=
  nonnegative_ite (p 115) (nonnegative646 p) (nonnegative616 p)
def d4468 (p : Pattern) : Int := if p 71 then d4467 p else d543 p
theorem agree4468 (p q : Pattern) (h : Agree support p q) : d4468 p = d4468 q := by
  simp only [d4468, h 71 (by decide), agree4467 p q h, agree543 p q h]
theorem nonnegative4468 (p : Pattern) : 0 ≤ d4468 p :=
  nonnegative_ite (p 71) (nonnegative4467 p) (nonnegative543 p)
def d4469 (p : Pattern) : Int := if p 49 then d4468 p else d4466 p
theorem agree4469 (p q : Pattern) (h : Agree support p q) : d4469 p = d4469 q := by
  simp only [d4469, h 49 (by decide), agree4468 p q h, agree4466 p q h]
theorem nonnegative4469 (p : Pattern) : 0 ≤ d4469 p :=
  nonnegative_ite (p 49) (nonnegative4468 p) (nonnegative4466 p)
def d4470 (p : Pattern) : Int := if p 48 then d4469 p else d4464 p
theorem agree4470 (p q : Pattern) (h : Agree support p q) : d4470 p = d4470 q := by
  simp only [d4470, h 48 (by decide), agree4469 p q h, agree4464 p q h]
theorem nonnegative4470 (p : Pattern) : 0 ≤ d4470 p :=
  nonnegative_ite (p 48) (nonnegative4469 p) (nonnegative4464 p)
def d4471 (p : Pattern) : Int := if p 160 then d0 p else d4206 p
theorem agree4471 (p q : Pattern) (h : Agree support p q) : d4471 p = d4471 q := by
  simp only [d4471, h 160 (by decide), agree0 p q h, agree4206 p q h]
theorem nonnegative4471 (p : Pattern) : 0 ≤ d4471 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative4206 p)
def d4472 (p : Pattern) : Int := if p 160 then d0 p else d4205 p
theorem agree4472 (p q : Pattern) (h : Agree support p q) : d4472 p = d4472 q := by
  simp only [d4472, h 160 (by decide), agree0 p q h, agree4205 p q h]
theorem nonnegative4472 (p : Pattern) : 0 ≤ d4472 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative4205 p)
def d4473 (p : Pattern) : Int := if p 204 then d1 p else d0 p
theorem agree4473 (p q : Pattern) (h : Agree support p q) : d4473 p = d4473 q := by
  simp only [d4473, h 204 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4473 (p : Pattern) : 0 ≤ d4473 p :=
  nonnegative_ite (p 204) (nonnegative1 p) (nonnegative0 p)
def d4474 (p : Pattern) : Int := if p 204 then d0 p else d1 p
theorem agree4474 (p q : Pattern) (h : Agree support p q) : d4474 p = d4474 q := by
  simp only [d4474, h 204 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4474 (p : Pattern) : 0 ≤ d4474 p :=
  nonnegative_ite (p 204) (nonnegative0 p) (nonnegative1 p)
def d4475 (p : Pattern) : Int := if p 182 then d4474 p else d0 p
theorem agree4475 (p q : Pattern) (h : Agree support p q) : d4475 p = d4475 q := by
  simp only [d4475, h 182 (by decide), agree4474 p q h, agree0 p q h]
theorem nonnegative4475 (p : Pattern) : 0 ≤ d4475 p :=
  nonnegative_ite (p 182) (nonnegative4474 p) (nonnegative0 p)
def d4476 (p : Pattern) : Int := if p 160 then d0 p else d4475 p
theorem agree4476 (p q : Pattern) (h : Agree support p q) : d4476 p = d4476 q := by
  simp only [d4476, h 160 (by decide), agree0 p q h, agree4475 p q h]
theorem nonnegative4476 (p : Pattern) : 0 ≤ d4476 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative4475 p)
def d4477 (p : Pattern) : Int := if p 163 then d18 p else d14 p
theorem agree4477 (p q : Pattern) (h : Agree support p q) : d4477 p = d4477 q := by
  simp only [d4477, h 163 (by decide), agree18 p q h, agree14 p q h]
theorem nonnegative4477 (p : Pattern) : 0 ≤ d4477 p :=
  nonnegative_ite (p 163) (nonnegative18 p) (nonnegative14 p)
def d4478 (p : Pattern) : Int := if p 162 then d4477 p else d14 p
theorem agree4478 (p q : Pattern) (h : Agree support p q) : d4478 p = d4478 q := by
  simp only [d4478, h 162 (by decide), agree4477 p q h, agree14 p q h]
theorem nonnegative4478 (p : Pattern) : 0 ≤ d4478 p :=
  nonnegative_ite (p 162) (nonnegative4477 p) (nonnegative14 p)
def d4479 (p : Pattern) : Int := if p 163 then d12 p else d24 p
theorem agree4479 (p q : Pattern) (h : Agree support p q) : d4479 p = d4479 q := by
  simp only [d4479, h 163 (by decide), agree12 p q h, agree24 p q h]
theorem nonnegative4479 (p : Pattern) : 0 ≤ d4479 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative24 p)
def d4480 (p : Pattern) : Int := if p 162 then d4479 p else d4477 p
theorem agree4480 (p q : Pattern) (h : Agree support p q) : d4480 p = d4480 q := by
  simp only [d4480, h 162 (by decide), agree4479 p q h, agree4477 p q h]
theorem nonnegative4480 (p : Pattern) : 0 ≤ d4480 p :=
  nonnegative_ite (p 162) (nonnegative4479 p) (nonnegative4477 p)
def d4481 (p : Pattern) : Int := if p 161 then d4480 p else d4478 p
theorem agree4481 (p q : Pattern) (h : Agree support p q) : d4481 p = d4481 q := by
  simp only [d4481, h 161 (by decide), agree4480 p q h, agree4478 p q h]
theorem nonnegative4481 (p : Pattern) : 0 ≤ d4481 p :=
  nonnegative_ite (p 161) (nonnegative4480 p) (nonnegative4478 p)
def d4482 (p : Pattern) : Int := if p 163 then d31 p else d14 p
theorem agree4482 (p q : Pattern) (h : Agree support p q) : d4482 p = d4482 q := by
  simp only [d4482, h 163 (by decide), agree31 p q h, agree14 p q h]
theorem nonnegative4482 (p : Pattern) : 0 ≤ d4482 p :=
  nonnegative_ite (p 163) (nonnegative31 p) (nonnegative14 p)
def d4483 (p : Pattern) : Int := if p 163 then d24 p else d18 p
theorem agree4483 (p q : Pattern) (h : Agree support p q) : d4483 p = d4483 q := by
  simp only [d4483, h 163 (by decide), agree24 p q h, agree18 p q h]
theorem nonnegative4483 (p : Pattern) : 0 ≤ d4483 p :=
  nonnegative_ite (p 163) (nonnegative24 p) (nonnegative18 p)
def d4484 (p : Pattern) : Int := if p 162 then d4483 p else d4482 p
theorem agree4484 (p q : Pattern) (h : Agree support p q) : d4484 p = d4484 q := by
  simp only [d4484, h 162 (by decide), agree4483 p q h, agree4482 p q h]
theorem nonnegative4484 (p : Pattern) : 0 ≤ d4484 p :=
  nonnegative_ite (p 162) (nonnegative4483 p) (nonnegative4482 p)
def d4485 (p : Pattern) : Int := if p 163 then d58 p else d18 p
theorem agree4485 (p q : Pattern) (h : Agree support p q) : d4485 p = d4485 q := by
  simp only [d4485, h 163 (by decide), agree58 p q h, agree18 p q h]
theorem nonnegative4485 (p : Pattern) : 0 ≤ d4485 p :=
  nonnegative_ite (p 163) (nonnegative58 p) (nonnegative18 p)
def d4486 (p : Pattern) : Int := if p 163 then d12 p else d40 p
theorem agree4486 (p q : Pattern) (h : Agree support p q) : d4486 p = d4486 q := by
  simp only [d4486, h 163 (by decide), agree12 p q h, agree40 p q h]
theorem nonnegative4486 (p : Pattern) : 0 ≤ d4486 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative40 p)
def d4487 (p : Pattern) : Int := if p 162 then d4486 p else d4485 p
theorem agree4487 (p q : Pattern) (h : Agree support p q) : d4487 p = d4487 q := by
  simp only [d4487, h 162 (by decide), agree4486 p q h, agree4485 p q h]
theorem nonnegative4487 (p : Pattern) : 0 ≤ d4487 p :=
  nonnegative_ite (p 162) (nonnegative4486 p) (nonnegative4485 p)
def d4488 (p : Pattern) : Int := if p 161 then d4487 p else d4484 p
theorem agree4488 (p q : Pattern) (h : Agree support p q) : d4488 p = d4488 q := by
  simp only [d4488, h 161 (by decide), agree4487 p q h, agree4484 p q h]
theorem nonnegative4488 (p : Pattern) : 0 ≤ d4488 p :=
  nonnegative_ite (p 161) (nonnegative4487 p) (nonnegative4484 p)
def d4489 (p : Pattern) : Int := if p 141 then d4488 p else d4481 p
theorem agree4489 (p q : Pattern) (h : Agree support p q) : d4489 p = d4489 q := by
  simp only [d4489, h 141 (by decide), agree4488 p q h, agree4481 p q h]
theorem nonnegative4489 (p : Pattern) : 0 ≤ d4489 p :=
  nonnegative_ite (p 141) (nonnegative4488 p) (nonnegative4481 p)
def d4490 (p : Pattern) : Int := if p 163 then d35 p else d31 p
theorem agree4490 (p q : Pattern) (h : Agree support p q) : d4490 p = d4490 q := by
  simp only [d4490, h 163 (by decide), agree35 p q h, agree31 p q h]
theorem nonnegative4490 (p : Pattern) : 0 ≤ d4490 p :=
  nonnegative_ite (p 163) (nonnegative35 p) (nonnegative31 p)
def d4491 (p : Pattern) : Int := if p 162 then d4486 p else d4490 p
theorem agree4491 (p q : Pattern) (h : Agree support p q) : d4491 p = d4491 q := by
  simp only [d4491, h 162 (by decide), agree4486 p q h, agree4490 p q h]
theorem nonnegative4491 (p : Pattern) : 0 ≤ d4491 p :=
  nonnegative_ite (p 162) (nonnegative4486 p) (nonnegative4490 p)
def d4492 (p : Pattern) : Int := if p 161 then d12 p else d4491 p
theorem agree4492 (p q : Pattern) (h : Agree support p q) : d4492 p = d4492 q := by
  simp only [d4492, h 161 (by decide), agree12 p q h, agree4491 p q h]
theorem nonnegative4492 (p : Pattern) : 0 ≤ d4492 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4491 p)
def d4493 (p : Pattern) : Int := if p 160 then d4492 p else d4481 p
theorem agree4493 (p q : Pattern) (h : Agree support p q) : d4493 p = d4493 q := by
  simp only [d4493, h 160 (by decide), agree4492 p q h, agree4481 p q h]
theorem nonnegative4493 (p : Pattern) : 0 ≤ d4493 p :=
  nonnegative_ite (p 160) (nonnegative4492 p) (nonnegative4481 p)
def d4494 (p : Pattern) : Int := if p 163 then d12 p else d35 p
theorem agree4494 (p q : Pattern) (h : Agree support p q) : d4494 p = d4494 q := by
  simp only [d4494, h 163 (by decide), agree12 p q h, agree35 p q h]
theorem nonnegative4494 (p : Pattern) : 0 ≤ d4494 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative35 p)
def d4495 (p : Pattern) : Int := if p 162 then d12 p else d4494 p
theorem agree4495 (p q : Pattern) (h : Agree support p q) : d4495 p = d4495 q := by
  simp only [d4495, h 162 (by decide), agree12 p q h, agree4494 p q h]
theorem nonnegative4495 (p : Pattern) : 0 ≤ d4495 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4494 p)
def d4496 (p : Pattern) : Int := if p 161 then d12 p else d4495 p
theorem agree4496 (p q : Pattern) (h : Agree support p q) : d4496 p = d4496 q := by
  simp only [d4496, h 161 (by decide), agree12 p q h, agree4495 p q h]
theorem nonnegative4496 (p : Pattern) : 0 ≤ d4496 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4495 p)
def d4497 (p : Pattern) : Int := if p 160 then d4496 p else d4488 p
theorem agree4497 (p q : Pattern) (h : Agree support p q) : d4497 p = d4497 q := by
  simp only [d4497, h 160 (by decide), agree4496 p q h, agree4488 p q h]
theorem nonnegative4497 (p : Pattern) : 0 ≤ d4497 p :=
  nonnegative_ite (p 160) (nonnegative4496 p) (nonnegative4488 p)
def d4498 (p : Pattern) : Int := if p 141 then d4497 p else d4493 p
theorem agree4498 (p q : Pattern) (h : Agree support p q) : d4498 p = d4498 q := by
  simp only [d4498, h 141 (by decide), agree4497 p q h, agree4493 p q h]
theorem nonnegative4498 (p : Pattern) : 0 ≤ d4498 p :=
  nonnegative_ite (p 141) (nonnegative4497 p) (nonnegative4493 p)
def d4499 (p : Pattern) : Int := if p 138 then d4498 p else d4489 p
theorem agree4499 (p q : Pattern) (h : Agree support p q) : d4499 p = d4499 q := by
  simp only [d4499, h 138 (by decide), agree4498 p q h, agree4489 p q h]
theorem nonnegative4499 (p : Pattern) : 0 ≤ d4499 p :=
  nonnegative_ite (p 138) (nonnegative4498 p) (nonnegative4489 p)
def d4500 (p : Pattern) : Int := if p 163 then d40 p else d24 p
theorem agree4500 (p q : Pattern) (h : Agree support p q) : d4500 p = d4500 q := by
  simp only [d4500, h 163 (by decide), agree40 p q h, agree24 p q h]
theorem nonnegative4500 (p : Pattern) : 0 ≤ d4500 p :=
  nonnegative_ite (p 163) (nonnegative40 p) (nonnegative24 p)
def d4501 (p : Pattern) : Int := if p 162 then d4486 p else d4500 p
theorem agree4501 (p q : Pattern) (h : Agree support p q) : d4501 p = d4501 q := by
  simp only [d4501, h 162 (by decide), agree4486 p q h, agree4500 p q h]
theorem nonnegative4501 (p : Pattern) : 0 ≤ d4501 p :=
  nonnegative_ite (p 162) (nonnegative4486 p) (nonnegative4500 p)
def d4502 (p : Pattern) : Int := if p 162 then d12 p else d4486 p
theorem agree4502 (p q : Pattern) (h : Agree support p q) : d4502 p = d4502 q := by
  simp only [d4502, h 162 (by decide), agree12 p q h, agree4486 p q h]
theorem nonnegative4502 (p : Pattern) : 0 ≤ d4502 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4486 p)
def d4503 (p : Pattern) : Int := if p 161 then d4502 p else d4501 p
theorem agree4503 (p q : Pattern) (h : Agree support p q) : d4503 p = d4503 q := by
  simp only [d4503, h 161 (by decide), agree4502 p q h, agree4501 p q h]
theorem nonnegative4503 (p : Pattern) : 0 ≤ d4503 p :=
  nonnegative_ite (p 161) (nonnegative4502 p) (nonnegative4501 p)
def d4504 (p : Pattern) : Int := if p 161 then d12 p else d4502 p
theorem agree4504 (p q : Pattern) (h : Agree support p q) : d4504 p = d4504 q := by
  simp only [d4504, h 161 (by decide), agree12 p q h, agree4502 p q h]
theorem nonnegative4504 (p : Pattern) : 0 ≤ d4504 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4502 p)
def d4505 (p : Pattern) : Int := if p 160 then d4504 p else d4503 p
theorem agree4505 (p q : Pattern) (h : Agree support p q) : d4505 p = d4505 q := by
  simp only [d4505, h 160 (by decide), agree4504 p q h, agree4503 p q h]
theorem nonnegative4505 (p : Pattern) : 0 ≤ d4505 p :=
  nonnegative_ite (p 160) (nonnegative4504 p) (nonnegative4503 p)
def d4506 (p : Pattern) : Int := if p 160 then d12 p else d4504 p
theorem agree4506 (p q : Pattern) (h : Agree support p q) : d4506 p = d4506 q := by
  simp only [d4506, h 160 (by decide), agree12 p q h, agree4504 p q h]
theorem nonnegative4506 (p : Pattern) : 0 ≤ d4506 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4504 p)
def d4507 (p : Pattern) : Int := if p 141 then d4506 p else d4505 p
theorem agree4507 (p q : Pattern) (h : Agree support p q) : d4507 p = d4507 q := by
  simp only [d4507, h 141 (by decide), agree4506 p q h, agree4505 p q h]
theorem nonnegative4507 (p : Pattern) : 0 ≤ d4507 p :=
  nonnegative_ite (p 141) (nonnegative4506 p) (nonnegative4505 p)
def d4508 (p : Pattern) : Int := if p 138 then d4507 p else d4498 p
theorem agree4508 (p q : Pattern) (h : Agree support p q) : d4508 p = d4508 q := by
  simp only [d4508, h 138 (by decide), agree4507 p q h, agree4498 p q h]
theorem nonnegative4508 (p : Pattern) : 0 ≤ d4508 p :=
  nonnegative_ite (p 138) (nonnegative4507 p) (nonnegative4498 p)
def d4509 (p : Pattern) : Int := if p 116 then d4508 p else d4499 p
theorem agree4509 (p q : Pattern) (h : Agree support p q) : d4509 p = d4509 q := by
  simp only [d4509, h 116 (by decide), agree4508 p q h, agree4499 p q h]
theorem nonnegative4509 (p : Pattern) : 0 ≤ d4509 p :=
  nonnegative_ite (p 116) (nonnegative4508 p) (nonnegative4499 p)
def d4510 (p : Pattern) : Int := if p 138 then d12 p else d4498 p
theorem agree4510 (p q : Pattern) (h : Agree support p q) : d4510 p = d4510 q := by
  simp only [d4510, h 138 (by decide), agree12 p q h, agree4498 p q h]
theorem nonnegative4510 (p : Pattern) : 0 ≤ d4510 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4498 p)
def d4511 (p : Pattern) : Int := if p 116 then d4510 p else d4499 p
theorem agree4511 (p q : Pattern) (h : Agree support p q) : d4511 p = d4511 q := by
  simp only [d4511, h 116 (by decide), agree4510 p q h, agree4499 p q h]
theorem nonnegative4511 (p : Pattern) : 0 ≤ d4511 p :=
  nonnegative_ite (p 116) (nonnegative4510 p) (nonnegative4499 p)
def d4512 (p : Pattern) : Int := if p 115 then d4511 p else d4509 p
theorem agree4512 (p q : Pattern) (h : Agree support p q) : d4512 p = d4512 q := by
  simp only [d4512, h 115 (by decide), agree4511 p q h, agree4509 p q h]
theorem nonnegative4512 (p : Pattern) : 0 ≤ d4512 p :=
  nonnegative_ite (p 115) (nonnegative4511 p) (nonnegative4509 p)
def d4513 (p : Pattern) : Int := if p 163 then d107 p else d103 p
theorem agree4513 (p q : Pattern) (h : Agree support p q) : d4513 p = d4513 q := by
  simp only [d4513, h 163 (by decide), agree107 p q h, agree103 p q h]
theorem nonnegative4513 (p : Pattern) : 0 ≤ d4513 p :=
  nonnegative_ite (p 163) (nonnegative107 p) (nonnegative103 p)
def d4514 (p : Pattern) : Int := if p 162 then d4513 p else d103 p
theorem agree4514 (p q : Pattern) (h : Agree support p q) : d4514 p = d4514 q := by
  simp only [d4514, h 162 (by decide), agree4513 p q h, agree103 p q h]
theorem nonnegative4514 (p : Pattern) : 0 ≤ d4514 p :=
  nonnegative_ite (p 162) (nonnegative4513 p) (nonnegative103 p)
def d4515 (p : Pattern) : Int := if p 163 then d12 p else d58 p
theorem agree4515 (p q : Pattern) (h : Agree support p q) : d4515 p = d4515 q := by
  simp only [d4515, h 163 (by decide), agree12 p q h, agree58 p q h]
theorem nonnegative4515 (p : Pattern) : 0 ≤ d4515 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative58 p)
def d4516 (p : Pattern) : Int := if p 162 then d4515 p else d4513 p
theorem agree4516 (p q : Pattern) (h : Agree support p q) : d4516 p = d4516 q := by
  simp only [d4516, h 162 (by decide), agree4515 p q h, agree4513 p q h]
theorem nonnegative4516 (p : Pattern) : 0 ≤ d4516 p :=
  nonnegative_ite (p 162) (nonnegative4515 p) (nonnegative4513 p)
def d4517 (p : Pattern) : Int := if p 161 then d4516 p else d4514 p
theorem agree4517 (p q : Pattern) (h : Agree support p q) : d4517 p = d4517 q := by
  simp only [d4517, h 161 (by decide), agree4516 p q h, agree4514 p q h]
theorem nonnegative4517 (p : Pattern) : 0 ≤ d4517 p :=
  nonnegative_ite (p 161) (nonnegative4516 p) (nonnegative4514 p)
def d4518 (p : Pattern) : Int := if p 163 then d116 p else d103 p
theorem agree4518 (p q : Pattern) (h : Agree support p q) : d4518 p = d4518 q := by
  simp only [d4518, h 163 (by decide), agree116 p q h, agree103 p q h]
theorem nonnegative4518 (p : Pattern) : 0 ≤ d4518 p :=
  nonnegative_ite (p 163) (nonnegative116 p) (nonnegative103 p)
def d4519 (p : Pattern) : Int := if p 163 then d58 p else d107 p
theorem agree4519 (p q : Pattern) (h : Agree support p q) : d4519 p = d4519 q := by
  simp only [d4519, h 163 (by decide), agree58 p q h, agree107 p q h]
theorem nonnegative4519 (p : Pattern) : 0 ≤ d4519 p :=
  nonnegative_ite (p 163) (nonnegative58 p) (nonnegative107 p)
def d4520 (p : Pattern) : Int := if p 162 then d4519 p else d4518 p
theorem agree4520 (p q : Pattern) (h : Agree support p q) : d4520 p = d4520 q := by
  simp only [d4520, h 162 (by decide), agree4519 p q h, agree4518 p q h]
theorem nonnegative4520 (p : Pattern) : 0 ≤ d4520 p :=
  nonnegative_ite (p 162) (nonnegative4519 p) (nonnegative4518 p)
def d4521 (p : Pattern) : Int := if p 163 then d40 p else d107 p
theorem agree4521 (p q : Pattern) (h : Agree support p q) : d4521 p = d4521 q := by
  simp only [d4521, h 163 (by decide), agree40 p q h, agree107 p q h]
theorem nonnegative4521 (p : Pattern) : 0 ≤ d4521 p :=
  nonnegative_ite (p 163) (nonnegative40 p) (nonnegative107 p)
def d4522 (p : Pattern) : Int := if p 162 then d12 p else d4521 p
theorem agree4522 (p q : Pattern) (h : Agree support p q) : d4522 p = d4522 q := by
  simp only [d4522, h 162 (by decide), agree12 p q h, agree4521 p q h]
theorem nonnegative4522 (p : Pattern) : 0 ≤ d4522 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4521 p)
def d4523 (p : Pattern) : Int := if p 161 then d4522 p else d4520 p
theorem agree4523 (p q : Pattern) (h : Agree support p q) : d4523 p = d4523 q := by
  simp only [d4523, h 161 (by decide), agree4522 p q h, agree4520 p q h]
theorem nonnegative4523 (p : Pattern) : 0 ≤ d4523 p :=
  nonnegative_ite (p 161) (nonnegative4522 p) (nonnegative4520 p)
def d4524 (p : Pattern) : Int := if p 141 then d4523 p else d4517 p
theorem agree4524 (p q : Pattern) (h : Agree support p q) : d4524 p = d4524 q := by
  simp only [d4524, h 141 (by decide), agree4523 p q h, agree4517 p q h]
theorem nonnegative4524 (p : Pattern) : 0 ≤ d4524 p :=
  nonnegative_ite (p 141) (nonnegative4523 p) (nonnegative4517 p)
def d4525 (p : Pattern) : Int := if p 163 then d120 p else d116 p
theorem agree4525 (p q : Pattern) (h : Agree support p q) : d4525 p = d4525 q := by
  simp only [d4525, h 163 (by decide), agree120 p q h, agree116 p q h]
theorem nonnegative4525 (p : Pattern) : 0 ≤ d4525 p :=
  nonnegative_ite (p 163) (nonnegative120 p) (nonnegative116 p)
def d4526 (p : Pattern) : Int := if p 162 then d12 p else d4525 p
theorem agree4526 (p q : Pattern) (h : Agree support p q) : d4526 p = d4526 q := by
  simp only [d4526, h 162 (by decide), agree12 p q h, agree4525 p q h]
theorem nonnegative4526 (p : Pattern) : 0 ≤ d4526 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4525 p)
def d4527 (p : Pattern) : Int := if p 161 then d12 p else d4526 p
theorem agree4527 (p q : Pattern) (h : Agree support p q) : d4527 p = d4527 q := by
  simp only [d4527, h 161 (by decide), agree12 p q h, agree4526 p q h]
theorem nonnegative4527 (p : Pattern) : 0 ≤ d4527 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4526 p)
def d4528 (p : Pattern) : Int := if p 160 then d4527 p else d4517 p
theorem agree4528 (p q : Pattern) (h : Agree support p q) : d4528 p = d4528 q := by
  simp only [d4528, h 160 (by decide), agree4527 p q h, agree4517 p q h]
theorem nonnegative4528 (p : Pattern) : 0 ≤ d4528 p :=
  nonnegative_ite (p 160) (nonnegative4527 p) (nonnegative4517 p)
def d4529 (p : Pattern) : Int := if p 163 then d12 p else d120 p
theorem agree4529 (p q : Pattern) (h : Agree support p q) : d4529 p = d4529 q := by
  simp only [d4529, h 163 (by decide), agree12 p q h, agree120 p q h]
theorem nonnegative4529 (p : Pattern) : 0 ≤ d4529 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative120 p)
def d4530 (p : Pattern) : Int := if p 162 then d12 p else d4529 p
theorem agree4530 (p q : Pattern) (h : Agree support p q) : d4530 p = d4530 q := by
  simp only [d4530, h 162 (by decide), agree12 p q h, agree4529 p q h]
theorem nonnegative4530 (p : Pattern) : 0 ≤ d4530 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4529 p)
def d4531 (p : Pattern) : Int := if p 161 then d12 p else d4530 p
theorem agree4531 (p q : Pattern) (h : Agree support p q) : d4531 p = d4531 q := by
  simp only [d4531, h 161 (by decide), agree12 p q h, agree4530 p q h]
theorem nonnegative4531 (p : Pattern) : 0 ≤ d4531 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4530 p)
def d4532 (p : Pattern) : Int := if p 160 then d4531 p else d4523 p
theorem agree4532 (p q : Pattern) (h : Agree support p q) : d4532 p = d4532 q := by
  simp only [d4532, h 160 (by decide), agree4531 p q h, agree4523 p q h]
theorem nonnegative4532 (p : Pattern) : 0 ≤ d4532 p :=
  nonnegative_ite (p 160) (nonnegative4531 p) (nonnegative4523 p)
def d4533 (p : Pattern) : Int := if p 141 then d4532 p else d4528 p
theorem agree4533 (p q : Pattern) (h : Agree support p q) : d4533 p = d4533 q := by
  simp only [d4533, h 141 (by decide), agree4532 p q h, agree4528 p q h]
theorem nonnegative4533 (p : Pattern) : 0 ≤ d4533 p :=
  nonnegative_ite (p 141) (nonnegative4532 p) (nonnegative4528 p)
def d4534 (p : Pattern) : Int := if p 138 then d4533 p else d4524 p
theorem agree4534 (p q : Pattern) (h : Agree support p q) : d4534 p = d4534 q := by
  simp only [d4534, h 138 (by decide), agree4533 p q h, agree4524 p q h]
theorem nonnegative4534 (p : Pattern) : 0 ≤ d4534 p :=
  nonnegative_ite (p 138) (nonnegative4533 p) (nonnegative4524 p)
def d4535 (p : Pattern) : Int := if p 162 then d12 p else d4515 p
theorem agree4535 (p q : Pattern) (h : Agree support p q) : d4535 p = d4535 q := by
  simp only [d4535, h 162 (by decide), agree12 p q h, agree4515 p q h]
theorem nonnegative4535 (p : Pattern) : 0 ≤ d4535 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4515 p)
def d4536 (p : Pattern) : Int := if p 161 then d12 p else d4535 p
theorem agree4536 (p q : Pattern) (h : Agree support p q) : d4536 p = d4536 q := by
  simp only [d4536, h 161 (by decide), agree12 p q h, agree4535 p q h]
theorem nonnegative4536 (p : Pattern) : 0 ≤ d4536 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4535 p)
def d4537 (p : Pattern) : Int := if p 160 then d12 p else d4536 p
theorem agree4537 (p q : Pattern) (h : Agree support p q) : d4537 p = d4537 q := by
  simp only [d4537, h 160 (by decide), agree12 p q h, agree4536 p q h]
theorem nonnegative4537 (p : Pattern) : 0 ≤ d4537 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4536 p)
def d4538 (p : Pattern) : Int := if p 141 then d12 p else d4537 p
theorem agree4538 (p q : Pattern) (h : Agree support p q) : d4538 p = d4538 q := by
  simp only [d4538, h 141 (by decide), agree12 p q h, agree4537 p q h]
theorem nonnegative4538 (p : Pattern) : 0 ≤ d4538 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative4537 p)
def d4539 (p : Pattern) : Int := if p 138 then d4538 p else d4533 p
theorem agree4539 (p q : Pattern) (h : Agree support p q) : d4539 p = d4539 q := by
  simp only [d4539, h 138 (by decide), agree4538 p q h, agree4533 p q h]
theorem nonnegative4539 (p : Pattern) : 0 ≤ d4539 p :=
  nonnegative_ite (p 138) (nonnegative4538 p) (nonnegative4533 p)
def d4540 (p : Pattern) : Int := if p 116 then d4539 p else d4534 p
theorem agree4540 (p q : Pattern) (h : Agree support p q) : d4540 p = d4540 q := by
  simp only [d4540, h 116 (by decide), agree4539 p q h, agree4534 p q h]
theorem nonnegative4540 (p : Pattern) : 0 ≤ d4540 p :=
  nonnegative_ite (p 116) (nonnegative4539 p) (nonnegative4534 p)
def d4541 (p : Pattern) : Int := if p 138 then d12 p else d4533 p
theorem agree4541 (p q : Pattern) (h : Agree support p q) : d4541 p = d4541 q := by
  simp only [d4541, h 138 (by decide), agree12 p q h, agree4533 p q h]
theorem nonnegative4541 (p : Pattern) : 0 ≤ d4541 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4533 p)
def d4542 (p : Pattern) : Int := if p 116 then d4541 p else d4534 p
theorem agree4542 (p q : Pattern) (h : Agree support p q) : d4542 p = d4542 q := by
  simp only [d4542, h 116 (by decide), agree4541 p q h, agree4534 p q h]
theorem nonnegative4542 (p : Pattern) : 0 ≤ d4542 p :=
  nonnegative_ite (p 116) (nonnegative4541 p) (nonnegative4534 p)
def d4543 (p : Pattern) : Int := if p 115 then d4542 p else d4540 p
theorem agree4543 (p q : Pattern) (h : Agree support p q) : d4543 p = d4543 q := by
  simp only [d4543, h 115 (by decide), agree4542 p q h, agree4540 p q h]
theorem nonnegative4543 (p : Pattern) : 0 ≤ d4543 p :=
  nonnegative_ite (p 115) (nonnegative4542 p) (nonnegative4540 p)
def d4544 (p : Pattern) : Int := if p 71 then d4543 p else d4512 p
theorem agree4544 (p q : Pattern) (h : Agree support p q) : d4544 p = d4544 q := by
  simp only [d4544, h 71 (by decide), agree4543 p q h, agree4512 p q h]
theorem nonnegative4544 (p : Pattern) : 0 ≤ d4544 p :=
  nonnegative_ite (p 71) (nonnegative4543 p) (nonnegative4512 p)
def d4545 (p : Pattern) : Int := if p 49 then d4544 p else d4512 p
theorem agree4545 (p q : Pattern) (h : Agree support p q) : d4545 p = d4545 q := by
  simp only [d4545, h 49 (by decide), agree4544 p q h, agree4512 p q h]
theorem nonnegative4545 (p : Pattern) : 0 ≤ d4545 p :=
  nonnegative_ite (p 49) (nonnegative4544 p) (nonnegative4512 p)
def d4546 (p : Pattern) : Int := if p 162 then d4490 p else d31 p
theorem agree4546 (p q : Pattern) (h : Agree support p q) : d4546 p = d4546 q := by
  simp only [d4546, h 162 (by decide), agree4490 p q h, agree31 p q h]
theorem nonnegative4546 (p : Pattern) : 0 ≤ d4546 p :=
  nonnegative_ite (p 162) (nonnegative4490 p) (nonnegative31 p)
def d4547 (p : Pattern) : Int := if p 161 then d4491 p else d4546 p
theorem agree4547 (p q : Pattern) (h : Agree support p q) : d4547 p = d4547 q := by
  simp only [d4547, h 161 (by decide), agree4491 p q h, agree4546 p q h]
theorem nonnegative4547 (p : Pattern) : 0 ≤ d4547 p :=
  nonnegative_ite (p 161) (nonnegative4491 p) (nonnegative4546 p)
def d4548 (p : Pattern) : Int := if p 160 then d4547 p else d4481 p
theorem agree4548 (p q : Pattern) (h : Agree support p q) : d4548 p = d4548 q := by
  simp only [d4548, h 160 (by decide), agree4547 p q h, agree4481 p q h]
theorem nonnegative4548 (p : Pattern) : 0 ≤ d4548 p :=
  nonnegative_ite (p 160) (nonnegative4547 p) (nonnegative4481 p)
def d4549 (p : Pattern) : Int := if p 163 then d18 p else d31 p
theorem agree4549 (p q : Pattern) (h : Agree support p q) : d4549 p = d4549 q := by
  simp only [d4549, h 163 (by decide), agree18 p q h, agree31 p q h]
theorem nonnegative4549 (p : Pattern) : 0 ≤ d4549 p :=
  nonnegative_ite (p 163) (nonnegative18 p) (nonnegative31 p)
def d4550 (p : Pattern) : Int := if p 163 then d40 p else d35 p
theorem agree4550 (p q : Pattern) (h : Agree support p q) : d4550 p = d4550 q := by
  simp only [d4550, h 163 (by decide), agree40 p q h, agree35 p q h]
theorem nonnegative4550 (p : Pattern) : 0 ≤ d4550 p :=
  nonnegative_ite (p 163) (nonnegative40 p) (nonnegative35 p)
def d4551 (p : Pattern) : Int := if p 162 then d4550 p else d4549 p
theorem agree4551 (p q : Pattern) (h : Agree support p q) : d4551 p = d4551 q := by
  simp only [d4551, h 162 (by decide), agree4550 p q h, agree4549 p q h]
theorem nonnegative4551 (p : Pattern) : 0 ≤ d4551 p :=
  nonnegative_ite (p 162) (nonnegative4550 p) (nonnegative4549 p)
def d4552 (p : Pattern) : Int := if p 161 then d4495 p else d4551 p
theorem agree4552 (p q : Pattern) (h : Agree support p q) : d4552 p = d4552 q := by
  simp only [d4552, h 161 (by decide), agree4495 p q h, agree4551 p q h]
theorem nonnegative4552 (p : Pattern) : 0 ≤ d4552 p :=
  nonnegative_ite (p 161) (nonnegative4495 p) (nonnegative4551 p)
def d4553 (p : Pattern) : Int := if p 160 then d4552 p else d4488 p
theorem agree4553 (p q : Pattern) (h : Agree support p q) : d4553 p = d4553 q := by
  simp only [d4553, h 160 (by decide), agree4552 p q h, agree4488 p q h]
theorem nonnegative4553 (p : Pattern) : 0 ≤ d4553 p :=
  nonnegative_ite (p 160) (nonnegative4552 p) (nonnegative4488 p)
def d4554 (p : Pattern) : Int := if p 141 then d4553 p else d4548 p
theorem agree4554 (p q : Pattern) (h : Agree support p q) : d4554 p = d4554 q := by
  simp only [d4554, h 141 (by decide), agree4553 p q h, agree4548 p q h]
theorem nonnegative4554 (p : Pattern) : 0 ≤ d4554 p :=
  nonnegative_ite (p 141) (nonnegative4553 p) (nonnegative4548 p)
def d4555 (p : Pattern) : Int := if p 162 then d4490 p else d14 p
theorem agree4555 (p q : Pattern) (h : Agree support p q) : d4555 p = d4555 q := by
  simp only [d4555, h 162 (by decide), agree4490 p q h, agree14 p q h]
theorem nonnegative4555 (p : Pattern) : 0 ≤ d4555 p :=
  nonnegative_ite (p 162) (nonnegative4490 p) (nonnegative14 p)
def d4556 (p : Pattern) : Int := if p 161 then d4491 p else d4555 p
theorem agree4556 (p q : Pattern) (h : Agree support p q) : d4556 p = d4556 q := by
  simp only [d4556, h 161 (by decide), agree4491 p q h, agree4555 p q h]
theorem nonnegative4556 (p : Pattern) : 0 ≤ d4556 p :=
  nonnegative_ite (p 161) (nonnegative4491 p) (nonnegative4555 p)
def d4557 (p : Pattern) : Int := if p 163 then d191 p else d18 p
theorem agree4557 (p q : Pattern) (h : Agree support p q) : d4557 p = d4557 q := by
  simp only [d4557, h 163 (by decide), agree191 p q h, agree18 p q h]
theorem nonnegative4557 (p : Pattern) : 0 ≤ d4557 p :=
  nonnegative_ite (p 163) (nonnegative191 p) (nonnegative18 p)
def d4558 (p : Pattern) : Int := if p 162 then d12 p else d4557 p
theorem agree4558 (p q : Pattern) (h : Agree support p q) : d4558 p = d4558 q := by
  simp only [d4558, h 162 (by decide), agree12 p q h, agree4557 p q h]
theorem nonnegative4558 (p : Pattern) : 0 ≤ d4558 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4557 p)
def d4559 (p : Pattern) : Int := if p 161 then d12 p else d4558 p
theorem agree4559 (p q : Pattern) (h : Agree support p q) : d4559 p = d4559 q := by
  simp only [d4559, h 161 (by decide), agree12 p q h, agree4558 p q h]
theorem nonnegative4559 (p : Pattern) : 0 ≤ d4559 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4558 p)
end NetHack.Sokoban22Refined85
