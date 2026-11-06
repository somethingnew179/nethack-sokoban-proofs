/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes53
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6480 (p : Pattern) : Int := if p 162 then d6379 p else d6328 p
theorem agree6480 (p q : Pattern) (h : Agree support p q) : d6480 p = d6480 q := by
  simp only [d6480, h 162 (by decide), agree6379 p q h, agree6328 p q h]
theorem nonnegative6480 (p : Pattern) : 0 ≤ d6480 p :=
  nonnegative_ite (p 162) (nonnegative6379 p) (nonnegative6328 p)
def d6481 (p : Pattern) : Int := if p 161 then d6380 p else d6480 p
theorem agree6481 (p q : Pattern) (h : Agree support p q) : d6481 p = d6481 q := by
  simp only [d6481, h 161 (by decide), agree6380 p q h, agree6480 p q h]
theorem nonnegative6481 (p : Pattern) : 0 ≤ d6481 p :=
  nonnegative_ite (p 161) (nonnegative6380 p) (nonnegative6480 p)
def d6482 (p : Pattern) : Int := if p 204 then d12 p else d8 p
theorem agree6482 (p q : Pattern) (h : Agree support p q) : d6482 p = d6482 q := by
  simp only [d6482, h 204 (by decide), agree12 p q h, agree8 p q h]
theorem nonnegative6482 (p : Pattern) : 0 ≤ d6482 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative8 p)
def d6483 (p : Pattern) : Int := if p 182 then d6482 p else d8 p
theorem agree6483 (p q : Pattern) (h : Agree support p q) : d6483 p = d6483 q := by
  simp only [d6483, h 182 (by decide), agree6482 p q h, agree8 p q h]
theorem nonnegative6483 (p : Pattern) : 0 ≤ d6483 p :=
  nonnegative_ite (p 182) (nonnegative6482 p) (nonnegative8 p)
def d6484 (p : Pattern) : Int := if p 163 then d6483 p else d6330 p
theorem agree6484 (p q : Pattern) (h : Agree support p q) : d6484 p = d6484 q := by
  simp only [d6484, h 163 (by decide), agree6483 p q h, agree6330 p q h]
theorem nonnegative6484 (p : Pattern) : 0 ≤ d6484 p :=
  nonnegative_ite (p 163) (nonnegative6483 p) (nonnegative6330 p)
def d6485 (p : Pattern) : Int := if p 162 then d12 p else d6484 p
theorem agree6485 (p q : Pattern) (h : Agree support p q) : d6485 p = d6485 q := by
  simp only [d6485, h 162 (by decide), agree12 p q h, agree6484 p q h]
theorem nonnegative6485 (p : Pattern) : 0 ≤ d6485 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6484 p)
def d6486 (p : Pattern) : Int := if p 161 then d12 p else d6485 p
theorem agree6486 (p q : Pattern) (h : Agree support p q) : d6486 p = d6486 q := by
  simp only [d6486, h 161 (by decide), agree12 p q h, agree6485 p q h]
theorem nonnegative6486 (p : Pattern) : 0 ≤ d6486 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6485 p)
def d6487 (p : Pattern) : Int := if p 160 then d6486 p else d6481 p
theorem agree6487 (p q : Pattern) (h : Agree support p q) : d6487 p = d6487 q := by
  simp only [d6487, h 160 (by decide), agree6486 p q h, agree6481 p q h]
theorem nonnegative6487 (p : Pattern) : 0 ≤ d6487 p :=
  nonnegative_ite (p 160) (nonnegative6486 p) (nonnegative6481 p)
def d6488 (p : Pattern) : Int := if p 163 then d6362 p else d6330 p
theorem agree6488 (p q : Pattern) (h : Agree support p q) : d6488 p = d6488 q := by
  simp only [d6488, h 163 (by decide), agree6362 p q h, agree6330 p q h]
theorem nonnegative6488 (p : Pattern) : 0 ≤ d6488 p :=
  nonnegative_ite (p 163) (nonnegative6362 p) (nonnegative6330 p)
def d6489 (p : Pattern) : Int := if p 162 then d6488 p else d6355 p
theorem agree6489 (p q : Pattern) (h : Agree support p q) : d6489 p = d6489 q := by
  simp only [d6489, h 162 (by decide), agree6488 p q h, agree6355 p q h]
theorem nonnegative6489 (p : Pattern) : 0 ≤ d6489 p :=
  nonnegative_ite (p 162) (nonnegative6488 p) (nonnegative6355 p)
def d6490 (p : Pattern) : Int := if p 161 then d6384 p else d6489 p
theorem agree6490 (p q : Pattern) (h : Agree support p q) : d6490 p = d6490 q := by
  simp only [d6490, h 161 (by decide), agree6384 p q h, agree6489 p q h]
theorem nonnegative6490 (p : Pattern) : 0 ≤ d6490 p :=
  nonnegative_ite (p 161) (nonnegative6384 p) (nonnegative6489 p)
def d6491 (p : Pattern) : Int := if p 163 then d12 p else d6483 p
theorem agree6491 (p q : Pattern) (h : Agree support p q) : d6491 p = d6491 q := by
  simp only [d6491, h 163 (by decide), agree12 p q h, agree6483 p q h]
theorem nonnegative6491 (p : Pattern) : 0 ≤ d6491 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6483 p)
def d6492 (p : Pattern) : Int := if p 162 then d12 p else d6491 p
theorem agree6492 (p q : Pattern) (h : Agree support p q) : d6492 p = d6492 q := by
  simp only [d6492, h 162 (by decide), agree12 p q h, agree6491 p q h]
theorem nonnegative6492 (p : Pattern) : 0 ≤ d6492 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6491 p)
def d6493 (p : Pattern) : Int := if p 161 then d12 p else d6492 p
theorem agree6493 (p q : Pattern) (h : Agree support p q) : d6493 p = d6493 q := by
  simp only [d6493, h 161 (by decide), agree12 p q h, agree6492 p q h]
theorem nonnegative6493 (p : Pattern) : 0 ≤ d6493 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6492 p)
def d6494 (p : Pattern) : Int := if p 160 then d6493 p else d6490 p
theorem agree6494 (p q : Pattern) (h : Agree support p q) : d6494 p = d6494 q := by
  simp only [d6494, h 160 (by decide), agree6493 p q h, agree6490 p q h]
theorem nonnegative6494 (p : Pattern) : 0 ≤ d6494 p :=
  nonnegative_ite (p 160) (nonnegative6493 p) (nonnegative6490 p)
def d6495 (p : Pattern) : Int := if p 141 then d6494 p else d6487 p
theorem agree6495 (p q : Pattern) (h : Agree support p q) : d6495 p = d6495 q := by
  simp only [d6495, h 141 (by decide), agree6494 p q h, agree6487 p q h]
theorem nonnegative6495 (p : Pattern) : 0 ≤ d6495 p :=
  nonnegative_ite (p 141) (nonnegative6494 p) (nonnegative6487 p)
def d6496 (p : Pattern) : Int := if p 138 then d6495 p else d6479 p
theorem agree6496 (p q : Pattern) (h : Agree support p q) : d6496 p = d6496 q := by
  simp only [d6496, h 138 (by decide), agree6495 p q h, agree6479 p q h]
theorem nonnegative6496 (p : Pattern) : 0 ≤ d6496 p :=
  nonnegative_ite (p 138) (nonnegative6495 p) (nonnegative6479 p)
def d6497 (p : Pattern) : Int := if p 138 then d12 p else d6495 p
theorem agree6497 (p q : Pattern) (h : Agree support p q) : d6497 p = d6497 q := by
  simp only [d6497, h 138 (by decide), agree12 p q h, agree6495 p q h]
theorem nonnegative6497 (p : Pattern) : 0 ≤ d6497 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6495 p)
def d6498 (p : Pattern) : Int := if p 116 then d6497 p else d6496 p
theorem agree6498 (p q : Pattern) (h : Agree support p q) : d6498 p = d6498 q := by
  simp only [d6498, h 116 (by decide), agree6497 p q h, agree6496 p q h]
theorem nonnegative6498 (p : Pattern) : 0 ≤ d6498 p :=
  nonnegative_ite (p 116) (nonnegative6497 p) (nonnegative6496 p)
def d6499 (p : Pattern) : Int := if p 115 then d6498 p else d6398 p
theorem agree6499 (p q : Pattern) (h : Agree support p q) : d6499 p = d6499 q := by
  simp only [d6499, h 115 (by decide), agree6498 p q h, agree6398 p q h]
theorem nonnegative6499 (p : Pattern) : 0 ≤ d6499 p :=
  nonnegative_ite (p 115) (nonnegative6498 p) (nonnegative6398 p)
def d6500 (p : Pattern) : Int := if p 71 then d6499 p else d6401 p
theorem agree6500 (p q : Pattern) (h : Agree support p q) : d6500 p = d6500 q := by
  simp only [d6500, h 71 (by decide), agree6499 p q h, agree6401 p q h]
theorem nonnegative6500 (p : Pattern) : 0 ≤ d6500 p :=
  nonnegative_ite (p 71) (nonnegative6499 p) (nonnegative6401 p)
def d6501 (p : Pattern) : Int := if p 163 then d12 p else d6405 p
theorem agree6501 (p q : Pattern) (h : Agree support p q) : d6501 p = d6501 q := by
  simp only [d6501, h 163 (by decide), agree12 p q h, agree6405 p q h]
theorem nonnegative6501 (p : Pattern) : 0 ≤ d6501 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6405 p)
def d6502 (p : Pattern) : Int := if p 162 then d6501 p else d6425 p
theorem agree6502 (p q : Pattern) (h : Agree support p q) : d6502 p = d6502 q := by
  simp only [d6502, h 162 (by decide), agree6501 p q h, agree6425 p q h]
theorem nonnegative6502 (p : Pattern) : 0 ≤ d6502 p :=
  nonnegative_ite (p 162) (nonnegative6501 p) (nonnegative6425 p)
def d6503 (p : Pattern) : Int := if p 162 then d12 p else d6501 p
theorem agree6503 (p q : Pattern) (h : Agree support p q) : d6503 p = d6503 q := by
  simp only [d6503, h 162 (by decide), agree12 p q h, agree6501 p q h]
theorem nonnegative6503 (p : Pattern) : 0 ≤ d6503 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6501 p)
def d6504 (p : Pattern) : Int := if p 161 then d6503 p else d6502 p
theorem agree6504 (p q : Pattern) (h : Agree support p q) : d6504 p = d6504 q := by
  simp only [d6504, h 161 (by decide), agree6503 p q h, agree6502 p q h]
theorem nonnegative6504 (p : Pattern) : 0 ≤ d6504 p :=
  nonnegative_ite (p 161) (nonnegative6503 p) (nonnegative6502 p)
def d6505 (p : Pattern) : Int := if p 163 then d12 p else d6417 p
theorem agree6505 (p q : Pattern) (h : Agree support p q) : d6505 p = d6505 q := by
  simp only [d6505, h 163 (by decide), agree12 p q h, agree6417 p q h]
theorem nonnegative6505 (p : Pattern) : 0 ≤ d6505 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6417 p)
def d6506 (p : Pattern) : Int := if p 162 then d6505 p else d6432 p
theorem agree6506 (p q : Pattern) (h : Agree support p q) : d6506 p = d6506 q := by
  simp only [d6506, h 162 (by decide), agree6505 p q h, agree6432 p q h]
theorem nonnegative6506 (p : Pattern) : 0 ≤ d6506 p :=
  nonnegative_ite (p 162) (nonnegative6505 p) (nonnegative6432 p)
def d6507 (p : Pattern) : Int := if p 162 then d12 p else d6505 p
theorem agree6507 (p q : Pattern) (h : Agree support p q) : d6507 p = d6507 q := by
  simp only [d6507, h 162 (by decide), agree12 p q h, agree6505 p q h]
theorem nonnegative6507 (p : Pattern) : 0 ≤ d6507 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6505 p)
def d6508 (p : Pattern) : Int := if p 161 then d6507 p else d6506 p
theorem agree6508 (p q : Pattern) (h : Agree support p q) : d6508 p = d6508 q := by
  simp only [d6508, h 161 (by decide), agree6507 p q h, agree6506 p q h]
theorem nonnegative6508 (p : Pattern) : 0 ≤ d6508 p :=
  nonnegative_ite (p 161) (nonnegative6507 p) (nonnegative6506 p)
def d6509 (p : Pattern) : Int := if p 160 then d6508 p else d6504 p
theorem agree6509 (p q : Pattern) (h : Agree support p q) : d6509 p = d6509 q := by
  simp only [d6509, h 160 (by decide), agree6508 p q h, agree6504 p q h]
theorem nonnegative6509 (p : Pattern) : 0 ≤ d6509 p :=
  nonnegative_ite (p 160) (nonnegative6508 p) (nonnegative6504 p)
def d6510 (p : Pattern) : Int := if p 141 then d6509 p else d6423 p
theorem agree6510 (p q : Pattern) (h : Agree support p q) : d6510 p = d6510 q := by
  simp only [d6510, h 141 (by decide), agree6509 p q h, agree6423 p q h]
theorem nonnegative6510 (p : Pattern) : 0 ≤ d6510 p :=
  nonnegative_ite (p 141) (nonnegative6509 p) (nonnegative6423 p)
def d6511 (p : Pattern) : Int := if p 160 then d6447 p else d6504 p
theorem agree6511 (p q : Pattern) (h : Agree support p q) : d6511 p = d6511 q := by
  simp only [d6511, h 160 (by decide), agree6447 p q h, agree6504 p q h]
theorem nonnegative6511 (p : Pattern) : 0 ≤ d6511 p :=
  nonnegative_ite (p 160) (nonnegative6447 p) (nonnegative6504 p)
def d6512 (p : Pattern) : Int := if p 141 then d6511 p else d6444 p
theorem agree6512 (p q : Pattern) (h : Agree support p q) : d6512 p = d6512 q := by
  simp only [d6512, h 141 (by decide), agree6511 p q h, agree6444 p q h]
theorem nonnegative6512 (p : Pattern) : 0 ≤ d6512 p :=
  nonnegative_ite (p 141) (nonnegative6511 p) (nonnegative6444 p)
def d6513 (p : Pattern) : Int := if p 138 then d6512 p else d6510 p
theorem agree6513 (p q : Pattern) (h : Agree support p q) : d6513 p = d6513 q := by
  simp only [d6513, h 138 (by decide), agree6512 p q h, agree6510 p q h]
theorem nonnegative6513 (p : Pattern) : 0 ≤ d6513 p :=
  nonnegative_ite (p 138) (nonnegative6512 p) (nonnegative6510 p)
def d6514 (p : Pattern) : Int := if p 138 then d6454 p else d6512 p
theorem agree6514 (p q : Pattern) (h : Agree support p q) : d6514 p = d6514 q := by
  simp only [d6514, h 138 (by decide), agree6454 p q h, agree6512 p q h]
theorem nonnegative6514 (p : Pattern) : 0 ≤ d6514 p :=
  nonnegative_ite (p 138) (nonnegative6454 p) (nonnegative6512 p)
def d6515 (p : Pattern) : Int := if p 116 then d6514 p else d6513 p
theorem agree6515 (p q : Pattern) (h : Agree support p q) : d6515 p = d6515 q := by
  simp only [d6515, h 116 (by decide), agree6514 p q h, agree6513 p q h]
theorem nonnegative6515 (p : Pattern) : 0 ≤ d6515 p :=
  nonnegative_ite (p 116) (nonnegative6514 p) (nonnegative6513 p)
def d6516 (p : Pattern) : Int := if p 182 then d6413 p else d3 p
theorem agree6516 (p q : Pattern) (h : Agree support p q) : d6516 p = d6516 q := by
  simp only [d6516, h 182 (by decide), agree6413 p q h, agree3 p q h]
theorem nonnegative6516 (p : Pattern) : 0 ≤ d6516 p :=
  nonnegative_ite (p 182) (nonnegative6413 p) (nonnegative3 p)
def d6517 (p : Pattern) : Int := if p 163 then d6516 p else d6424 p
theorem agree6517 (p q : Pattern) (h : Agree support p q) : d6517 p = d6517 q := by
  simp only [d6517, h 163 (by decide), agree6516 p q h, agree6424 p q h]
theorem nonnegative6517 (p : Pattern) : 0 ≤ d6517 p :=
  nonnegative_ite (p 163) (nonnegative6516 p) (nonnegative6424 p)
def d6518 (p : Pattern) : Int := if p 162 then d6505 p else d6517 p
theorem agree6518 (p q : Pattern) (h : Agree support p q) : d6518 p = d6518 q := by
  simp only [d6518, h 162 (by decide), agree6505 p q h, agree6517 p q h]
theorem nonnegative6518 (p : Pattern) : 0 ≤ d6518 p :=
  nonnegative_ite (p 162) (nonnegative6505 p) (nonnegative6517 p)
def d6519 (p : Pattern) : Int := if p 182 then d12 p else d7 p
theorem agree6519 (p q : Pattern) (h : Agree support p q) : d6519 p = d6519 q := by
  simp only [d6519, h 182 (by decide), agree12 p q h, agree7 p q h]
theorem nonnegative6519 (p : Pattern) : 0 ≤ d6519 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7 p)
def d6520 (p : Pattern) : Int := if p 163 then d12 p else d6519 p
theorem agree6520 (p q : Pattern) (h : Agree support p q) : d6520 p = d6520 q := by
  simp only [d6520, h 163 (by decide), agree12 p q h, agree6519 p q h]
theorem nonnegative6520 (p : Pattern) : 0 ≤ d6520 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6519 p)
def d6521 (p : Pattern) : Int := if p 162 then d12 p else d6520 p
theorem agree6521 (p q : Pattern) (h : Agree support p q) : d6521 p = d6521 q := by
  simp only [d6521, h 162 (by decide), agree12 p q h, agree6520 p q h]
theorem nonnegative6521 (p : Pattern) : 0 ≤ d6521 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6520 p)
def d6522 (p : Pattern) : Int := if p 161 then d6521 p else d6518 p
theorem agree6522 (p q : Pattern) (h : Agree support p q) : d6522 p = d6522 q := by
  simp only [d6522, h 161 (by decide), agree6521 p q h, agree6518 p q h]
theorem nonnegative6522 (p : Pattern) : 0 ≤ d6522 p :=
  nonnegative_ite (p 161) (nonnegative6521 p) (nonnegative6518 p)
def d6523 (p : Pattern) : Int := if p 160 then d6522 p else d6410 p
theorem agree6523 (p q : Pattern) (h : Agree support p q) : d6523 p = d6523 q := by
  simp only [d6523, h 160 (by decide), agree6522 p q h, agree6410 p q h]
theorem nonnegative6523 (p : Pattern) : 0 ≤ d6523 p :=
  nonnegative_ite (p 160) (nonnegative6522 p) (nonnegative6410 p)
def d6524 (p : Pattern) : Int := if p 182 then d6413 p else d5 p
theorem agree6524 (p q : Pattern) (h : Agree support p q) : d6524 p = d6524 q := by
  simp only [d6524, h 182 (by decide), agree6413 p q h, agree5 p q h]
theorem nonnegative6524 (p : Pattern) : 0 ≤ d6524 p :=
  nonnegative_ite (p 182) (nonnegative6413 p) (nonnegative5 p)
def d6525 (p : Pattern) : Int := if p 163 then d6417 p else d6524 p
theorem agree6525 (p q : Pattern) (h : Agree support p q) : d6525 p = d6525 q := by
  simp only [d6525, h 163 (by decide), agree6417 p q h, agree6524 p q h]
theorem nonnegative6525 (p : Pattern) : 0 ≤ d6525 p :=
  nonnegative_ite (p 163) (nonnegative6417 p) (nonnegative6524 p)
def d6526 (p : Pattern) : Int := if p 162 then d6520 p else d6525 p
theorem agree6526 (p q : Pattern) (h : Agree support p q) : d6526 p = d6526 q := by
  simp only [d6526, h 162 (by decide), agree6520 p q h, agree6525 p q h]
theorem nonnegative6526 (p : Pattern) : 0 ≤ d6526 p :=
  nonnegative_ite (p 162) (nonnegative6520 p) (nonnegative6525 p)
def d6527 (p : Pattern) : Int := if p 162 then d12 p else d6351 p
theorem agree6527 (p q : Pattern) (h : Agree support p q) : d6527 p = d6527 q := by
  simp only [d6527, h 162 (by decide), agree12 p q h, agree6351 p q h]
theorem nonnegative6527 (p : Pattern) : 0 ≤ d6527 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6351 p)
def d6528 (p : Pattern) : Int := if p 161 then d6527 p else d6526 p
theorem agree6528 (p q : Pattern) (h : Agree support p q) : d6528 p = d6528 q := by
  simp only [d6528, h 161 (by decide), agree6527 p q h, agree6526 p q h]
theorem nonnegative6528 (p : Pattern) : 0 ≤ d6528 p :=
  nonnegative_ite (p 161) (nonnegative6527 p) (nonnegative6526 p)
def d6529 (p : Pattern) : Int := if p 160 then d6528 p else d6504 p
theorem agree6529 (p q : Pattern) (h : Agree support p q) : d6529 p = d6529 q := by
  simp only [d6529, h 160 (by decide), agree6528 p q h, agree6504 p q h]
theorem nonnegative6529 (p : Pattern) : 0 ≤ d6529 p :=
  nonnegative_ite (p 160) (nonnegative6528 p) (nonnegative6504 p)
def d6530 (p : Pattern) : Int := if p 141 then d6529 p else d6523 p
theorem agree6530 (p q : Pattern) (h : Agree support p q) : d6530 p = d6530 q := by
  simp only [d6530, h 141 (by decide), agree6529 p q h, agree6523 p q h]
theorem nonnegative6530 (p : Pattern) : 0 ≤ d6530 p :=
  nonnegative_ite (p 141) (nonnegative6529 p) (nonnegative6523 p)
def d6531 (p : Pattern) : Int := if p 163 then d6362 p else d6424 p
theorem agree6531 (p q : Pattern) (h : Agree support p q) : d6531 p = d6531 q := by
  simp only [d6531, h 163 (by decide), agree6362 p q h, agree6424 p q h]
theorem nonnegative6531 (p : Pattern) : 0 ≤ d6531 p :=
  nonnegative_ite (p 163) (nonnegative6362 p) (nonnegative6424 p)
def d6532 (p : Pattern) : Int := if p 162 then d6531 p else d6403 p
theorem agree6532 (p q : Pattern) (h : Agree support p q) : d6532 p = d6532 q := by
  simp only [d6532, h 162 (by decide), agree6531 p q h, agree6403 p q h]
theorem nonnegative6532 (p : Pattern) : 0 ≤ d6532 p :=
  nonnegative_ite (p 162) (nonnegative6531 p) (nonnegative6403 p)
def d6533 (p : Pattern) : Int := if p 161 then d6429 p else d6532 p
theorem agree6533 (p q : Pattern) (h : Agree support p q) : d6533 p = d6533 q := by
  simp only [d6533, h 161 (by decide), agree6429 p q h, agree6532 p q h]
theorem nonnegative6533 (p : Pattern) : 0 ≤ d6533 p :=
  nonnegative_ite (p 161) (nonnegative6429 p) (nonnegative6532 p)
def d6534 (p : Pattern) : Int := if p 160 then d6447 p else d6533 p
theorem agree6534 (p q : Pattern) (h : Agree support p q) : d6534 p = d6534 q := by
  simp only [d6534, h 160 (by decide), agree6447 p q h, agree6533 p q h]
theorem nonnegative6534 (p : Pattern) : 0 ≤ d6534 p :=
  nonnegative_ite (p 160) (nonnegative6447 p) (nonnegative6533 p)
def d6535 (p : Pattern) : Int := if p 162 then d6501 p else d6424 p
theorem agree6535 (p q : Pattern) (h : Agree support p q) : d6535 p = d6535 q := by
  simp only [d6535, h 162 (by decide), agree6501 p q h, agree6424 p q h]
theorem nonnegative6535 (p : Pattern) : 0 ≤ d6535 p :=
  nonnegative_ite (p 162) (nonnegative6501 p) (nonnegative6424 p)
def d6536 (p : Pattern) : Int := if p 161 then d6446 p else d6535 p
theorem agree6536 (p q : Pattern) (h : Agree support p q) : d6536 p = d6536 q := by
  simp only [d6536, h 161 (by decide), agree6446 p q h, agree6535 p q h]
theorem nonnegative6536 (p : Pattern) : 0 ≤ d6536 p :=
  nonnegative_ite (p 161) (nonnegative6446 p) (nonnegative6535 p)
def d6537 (p : Pattern) : Int := if p 162 then d12 p else d6335 p
theorem agree6537 (p q : Pattern) (h : Agree support p q) : d6537 p = d6537 q := by
  simp only [d6537, h 162 (by decide), agree12 p q h, agree6335 p q h]
theorem nonnegative6537 (p : Pattern) : 0 ≤ d6537 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6335 p)
def d6538 (p : Pattern) : Int := if p 161 then d12 p else d6537 p
theorem agree6538 (p q : Pattern) (h : Agree support p q) : d6538 p = d6538 q := by
  simp only [d6538, h 161 (by decide), agree12 p q h, agree6537 p q h]
theorem nonnegative6538 (p : Pattern) : 0 ≤ d6538 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6537 p)
def d6539 (p : Pattern) : Int := if p 160 then d6538 p else d6536 p
theorem agree6539 (p q : Pattern) (h : Agree support p q) : d6539 p = d6539 q := by
  simp only [d6539, h 160 (by decide), agree6538 p q h, agree6536 p q h]
theorem nonnegative6539 (p : Pattern) : 0 ≤ d6539 p :=
  nonnegative_ite (p 160) (nonnegative6538 p) (nonnegative6536 p)
def d6540 (p : Pattern) : Int := if p 141 then d6539 p else d6534 p
theorem agree6540 (p q : Pattern) (h : Agree support p q) : d6540 p = d6540 q := by
  simp only [d6540, h 141 (by decide), agree6539 p q h, agree6534 p q h]
theorem nonnegative6540 (p : Pattern) : 0 ≤ d6540 p :=
  nonnegative_ite (p 141) (nonnegative6539 p) (nonnegative6534 p)
def d6541 (p : Pattern) : Int := if p 138 then d6540 p else d6530 p
theorem agree6541 (p q : Pattern) (h : Agree support p q) : d6541 p = d6541 q := by
  simp only [d6541, h 138 (by decide), agree6540 p q h, agree6530 p q h]
theorem nonnegative6541 (p : Pattern) : 0 ≤ d6541 p :=
  nonnegative_ite (p 138) (nonnegative6540 p) (nonnegative6530 p)
def d6542 (p : Pattern) : Int := if p 163 then d6334 p else d6424 p
theorem agree6542 (p q : Pattern) (h : Agree support p q) : d6542 p = d6542 q := by
  simp only [d6542, h 163 (by decide), agree6334 p q h, agree6424 p q h]
theorem nonnegative6542 (p : Pattern) : 0 ≤ d6542 p :=
  nonnegative_ite (p 163) (nonnegative6334 p) (nonnegative6424 p)
def d6543 (p : Pattern) : Int := if p 162 then d6542 p else d6403 p
theorem agree6543 (p q : Pattern) (h : Agree support p q) : d6543 p = d6543 q := by
  simp only [d6543, h 162 (by decide), agree6542 p q h, agree6403 p q h]
theorem nonnegative6543 (p : Pattern) : 0 ≤ d6543 p :=
  nonnegative_ite (p 162) (nonnegative6542 p) (nonnegative6403 p)
def d6544 (p : Pattern) : Int := if p 163 then d6334 p else d6405 p
theorem agree6544 (p q : Pattern) (h : Agree support p q) : d6544 p = d6544 q := by
  simp only [d6544, h 163 (by decide), agree6334 p q h, agree6405 p q h]
theorem nonnegative6544 (p : Pattern) : 0 ≤ d6544 p :=
  nonnegative_ite (p 163) (nonnegative6334 p) (nonnegative6405 p)
def d6545 (p : Pattern) : Int := if p 162 then d12 p else d6544 p
theorem agree6545 (p q : Pattern) (h : Agree support p q) : d6545 p = d6545 q := by
  simp only [d6545, h 162 (by decide), agree12 p q h, agree6544 p q h]
theorem nonnegative6545 (p : Pattern) : 0 ≤ d6545 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6544 p)
def d6546 (p : Pattern) : Int := if p 161 then d6545 p else d6543 p
theorem agree6546 (p q : Pattern) (h : Agree support p q) : d6546 p = d6546 q := by
  simp only [d6546, h 161 (by decide), agree6545 p q h, agree6543 p q h]
theorem nonnegative6546 (p : Pattern) : 0 ≤ d6546 p :=
  nonnegative_ite (p 161) (nonnegative6545 p) (nonnegative6543 p)
def d6547 (p : Pattern) : Int := if p 163 then d6362 p else d6440 p
theorem agree6547 (p q : Pattern) (h : Agree support p q) : d6547 p = d6547 q := by
  simp only [d6547, h 163 (by decide), agree6362 p q h, agree6440 p q h]
theorem nonnegative6547 (p : Pattern) : 0 ≤ d6547 p :=
  nonnegative_ite (p 163) (nonnegative6362 p) (nonnegative6440 p)
def d6548 (p : Pattern) : Int := if p 162 then d12 p else d6547 p
theorem agree6548 (p q : Pattern) (h : Agree support p q) : d6548 p = d6548 q := by
  simp only [d6548, h 162 (by decide), agree12 p q h, agree6547 p q h]
theorem nonnegative6548 (p : Pattern) : 0 ≤ d6548 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6547 p)
def d6549 (p : Pattern) : Int := if p 161 then d12 p else d6548 p
theorem agree6549 (p q : Pattern) (h : Agree support p q) : d6549 p = d6549 q := by
  simp only [d6549, h 161 (by decide), agree12 p q h, agree6548 p q h]
theorem nonnegative6549 (p : Pattern) : 0 ≤ d6549 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6548 p)
def d6550 (p : Pattern) : Int := if p 160 then d6549 p else d6546 p
theorem agree6550 (p q : Pattern) (h : Agree support p q) : d6550 p = d6550 q := by
  simp only [d6550, h 160 (by decide), agree6549 p q h, agree6546 p q h]
theorem nonnegative6550 (p : Pattern) : 0 ≤ d6550 p :=
  nonnegative_ite (p 160) (nonnegative6549 p) (nonnegative6546 p)
def d6551 (p : Pattern) : Int := if p 141 then d6539 p else d6550 p
theorem agree6551 (p q : Pattern) (h : Agree support p q) : d6551 p = d6551 q := by
  simp only [d6551, h 141 (by decide), agree6539 p q h, agree6550 p q h]
theorem nonnegative6551 (p : Pattern) : 0 ≤ d6551 p :=
  nonnegative_ite (p 141) (nonnegative6539 p) (nonnegative6550 p)
def d6552 (p : Pattern) : Int := if p 138 then d12 p else d6551 p
theorem agree6552 (p q : Pattern) (h : Agree support p q) : d6552 p = d6552 q := by
  simp only [d6552, h 138 (by decide), agree12 p q h, agree6551 p q h]
theorem nonnegative6552 (p : Pattern) : 0 ≤ d6552 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6551 p)
def d6553 (p : Pattern) : Int := if p 116 then d6552 p else d6541 p
theorem agree6553 (p q : Pattern) (h : Agree support p q) : d6553 p = d6553 q := by
  simp only [d6553, h 116 (by decide), agree6552 p q h, agree6541 p q h]
theorem nonnegative6553 (p : Pattern) : 0 ≤ d6553 p :=
  nonnegative_ite (p 116) (nonnegative6552 p) (nonnegative6541 p)
def d6554 (p : Pattern) : Int := if p 115 then d6553 p else d6515 p
theorem agree6554 (p q : Pattern) (h : Agree support p q) : d6554 p = d6554 q := by
  simp only [d6554, h 115 (by decide), agree6553 p q h, agree6515 p q h]
theorem nonnegative6554 (p : Pattern) : 0 ≤ d6554 p :=
  nonnegative_ite (p 115) (nonnegative6553 p) (nonnegative6515 p)
def d6555 (p : Pattern) : Int := if p 71 then d6554 p else d6401 p
theorem agree6555 (p q : Pattern) (h : Agree support p q) : d6555 p = d6555 q := by
  simp only [d6555, h 71 (by decide), agree6554 p q h, agree6401 p q h]
theorem nonnegative6555 (p : Pattern) : 0 ≤ d6555 p :=
  nonnegative_ite (p 71) (nonnegative6554 p) (nonnegative6401 p)
def d6556 (p : Pattern) : Int := if p 49 then d6555 p else d6500 p
theorem agree6556 (p q : Pattern) (h : Agree support p q) : d6556 p = d6556 q := by
  simp only [d6556, h 49 (by decide), agree6555 p q h, agree6500 p q h]
theorem nonnegative6556 (p : Pattern) : 0 ≤ d6556 p :=
  nonnegative_ite (p 49) (nonnegative6555 p) (nonnegative6500 p)
def d6557 (p : Pattern) : Int := if p 48 then d6556 p else d6461 p
theorem agree6557 (p q : Pattern) (h : Agree support p q) : d6557 p = d6557 q := by
  simp only [d6557, h 48 (by decide), agree6556 p q h, agree6461 p q h]
theorem nonnegative6557 (p : Pattern) : 0 ≤ d6557 p :=
  nonnegative_ite (p 48) (nonnegative6556 p) (nonnegative6461 p)
def d6558 (p : Pattern) : Int := if p 246 then d0 p else d5842 p
theorem agree6558 (p q : Pattern) (h : Agree support p q) : d6558 p = d6558 q := by
  simp only [d6558, h 246 (by decide), agree0 p q h, agree5842 p q h]
theorem nonnegative6558 (p : Pattern) : 0 ≤ d6558 p :=
  nonnegative_ite (p 246) (nonnegative0 p) (nonnegative5842 p)
def d6559 (p : Pattern) : Int := if p 246 then d4 p else d0 p
theorem agree6559 (p q : Pattern) (h : Agree support p q) : d6559 p = d6559 q := by
  simp only [d6559, h 246 (by decide), agree4 p q h, agree0 p q h]
theorem nonnegative6559 (p : Pattern) : 0 ≤ d6559 p :=
  nonnegative_ite (p 246) (nonnegative4 p) (nonnegative0 p)
def d6560 (p : Pattern) : Int := if p 225 then d6559 p else d0 p
theorem agree6560 (p q : Pattern) (h : Agree support p q) : d6560 p = d6560 q := by
  simp only [d6560, h 225 (by decide), agree6559 p q h, agree0 p q h]
theorem nonnegative6560 (p : Pattern) : 0 ≤ d6560 p :=
  nonnegative_ite (p 225) (nonnegative6559 p) (nonnegative0 p)
def d6561 (p : Pattern) : Int := if p 224 then d6559 p else d6560 p
theorem agree6561 (p q : Pattern) (h : Agree support p q) : d6561 p = d6561 q := by
  simp only [d6561, h 224 (by decide), agree6559 p q h, agree6560 p q h]
theorem nonnegative6561 (p : Pattern) : 0 ≤ d6561 p :=
  nonnegative_ite (p 224) (nonnegative6559 p) (nonnegative6560 p)
def d6562 (p : Pattern) : Int := if p 204 then d6561 p else d0 p
theorem agree6562 (p q : Pattern) (h : Agree support p q) : d6562 p = d6562 q := by
  simp only [d6562, h 204 (by decide), agree6561 p q h, agree0 p q h]
theorem nonnegative6562 (p : Pattern) : 0 ≤ d6562 p :=
  nonnegative_ite (p 204) (nonnegative6561 p) (nonnegative0 p)
def d6563 (p : Pattern) : Int := if p 246 then d2 p else d0 p
theorem agree6563 (p q : Pattern) (h : Agree support p q) : d6563 p = d6563 q := by
  simp only [d6563, h 246 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative6563 (p : Pattern) : 0 ≤ d6563 p :=
  nonnegative_ite (p 246) (nonnegative2 p) (nonnegative0 p)
def d6564 (p : Pattern) : Int := if p 225 then d6563 p else d0 p
theorem agree6564 (p q : Pattern) (h : Agree support p q) : d6564 p = d6564 q := by
  simp only [d6564, h 225 (by decide), agree6563 p q h, agree0 p q h]
theorem nonnegative6564 (p : Pattern) : 0 ≤ d6564 p :=
  nonnegative_ite (p 225) (nonnegative6563 p) (nonnegative0 p)
def d6565 (p : Pattern) : Int := if p 224 then d6563 p else d6564 p
theorem agree6565 (p q : Pattern) (h : Agree support p q) : d6565 p = d6565 q := by
  simp only [d6565, h 224 (by decide), agree6563 p q h, agree6564 p q h]
theorem nonnegative6565 (p : Pattern) : 0 ≤ d6565 p :=
  nonnegative_ite (p 224) (nonnegative6563 p) (nonnegative6564 p)
def d6566 (p : Pattern) : Int := if p 204 then d12 p else d6565 p
theorem agree6566 (p q : Pattern) (h : Agree support p q) : d6566 p = d6566 q := by
  simp only [d6566, h 204 (by decide), agree12 p q h, agree6565 p q h]
theorem nonnegative6566 (p : Pattern) : 0 ≤ d6566 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6565 p)
def d6567 (p : Pattern) : Int := if p 182 then d6566 p else d6562 p
theorem agree6567 (p q : Pattern) (h : Agree support p q) : d6567 p = d6567 q := by
  simp only [d6567, h 182 (by decide), agree6566 p q h, agree6562 p q h]
theorem nonnegative6567 (p : Pattern) : 0 ≤ d6567 p :=
  nonnegative_ite (p 182) (nonnegative6566 p) (nonnegative6562 p)
def d6568 (p : Pattern) : Int := if p 246 then d8 p else d4 p
theorem agree6568 (p q : Pattern) (h : Agree support p q) : d6568 p = d6568 q := by
  simp only [d6568, h 246 (by decide), agree8 p q h, agree4 p q h]
theorem nonnegative6568 (p : Pattern) : 0 ≤ d6568 p :=
  nonnegative_ite (p 246) (nonnegative8 p) (nonnegative4 p)
def d6569 (p : Pattern) : Int := if p 225 then d6568 p else d4 p
theorem agree6569 (p q : Pattern) (h : Agree support p q) : d6569 p = d6569 q := by
  simp only [d6569, h 225 (by decide), agree6568 p q h, agree4 p q h]
theorem nonnegative6569 (p : Pattern) : 0 ≤ d6569 p :=
  nonnegative_ite (p 225) (nonnegative6568 p) (nonnegative4 p)
def d6570 (p : Pattern) : Int := if p 224 then d6568 p else d6569 p
theorem agree6570 (p q : Pattern) (h : Agree support p q) : d6570 p = d6570 q := by
  simp only [d6570, h 224 (by decide), agree6568 p q h, agree6569 p q h]
theorem nonnegative6570 (p : Pattern) : 0 ≤ d6570 p :=
  nonnegative_ite (p 224) (nonnegative6568 p) (nonnegative6569 p)
def d6571 (p : Pattern) : Int := if p 204 then d6570 p else d4 p
theorem agree6571 (p q : Pattern) (h : Agree support p q) : d6571 p = d6571 q := by
  simp only [d6571, h 204 (by decide), agree6570 p q h, agree4 p q h]
theorem nonnegative6571 (p : Pattern) : 0 ≤ d6571 p :=
  nonnegative_ite (p 204) (nonnegative6570 p) (nonnegative4 p)
def d6572 (p : Pattern) : Int := if p 246 then d6 p else d4 p
theorem agree6572 (p q : Pattern) (h : Agree support p q) : d6572 p = d6572 q := by
  simp only [d6572, h 246 (by decide), agree6 p q h, agree4 p q h]
theorem nonnegative6572 (p : Pattern) : 0 ≤ d6572 p :=
  nonnegative_ite (p 246) (nonnegative6 p) (nonnegative4 p)
def d6573 (p : Pattern) : Int := if p 225 then d6572 p else d4 p
theorem agree6573 (p q : Pattern) (h : Agree support p q) : d6573 p = d6573 q := by
  simp only [d6573, h 225 (by decide), agree6572 p q h, agree4 p q h]
theorem nonnegative6573 (p : Pattern) : 0 ≤ d6573 p :=
  nonnegative_ite (p 225) (nonnegative6572 p) (nonnegative4 p)
def d6574 (p : Pattern) : Int := if p 224 then d6572 p else d6573 p
theorem agree6574 (p q : Pattern) (h : Agree support p q) : d6574 p = d6574 q := by
  simp only [d6574, h 224 (by decide), agree6572 p q h, agree6573 p q h]
theorem nonnegative6574 (p : Pattern) : 0 ≤ d6574 p :=
  nonnegative_ite (p 224) (nonnegative6572 p) (nonnegative6573 p)
def d6575 (p : Pattern) : Int := if p 204 then d12 p else d6574 p
theorem agree6575 (p q : Pattern) (h : Agree support p q) : d6575 p = d6575 q := by
  simp only [d6575, h 204 (by decide), agree12 p q h, agree6574 p q h]
theorem nonnegative6575 (p : Pattern) : 0 ≤ d6575 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6574 p)
def d6576 (p : Pattern) : Int := if p 182 then d6575 p else d6571 p
theorem agree6576 (p q : Pattern) (h : Agree support p q) : d6576 p = d6576 q := by
  simp only [d6576, h 182 (by decide), agree6575 p q h, agree6571 p q h]
theorem nonnegative6576 (p : Pattern) : 0 ≤ d6576 p :=
  nonnegative_ite (p 182) (nonnegative6575 p) (nonnegative6571 p)
def d6577 (p : Pattern) : Int := if p 163 then d6576 p else d6567 p
theorem agree6577 (p q : Pattern) (h : Agree support p q) : d6577 p = d6577 q := by
  simp only [d6577, h 163 (by decide), agree6576 p q h, agree6567 p q h]
theorem nonnegative6577 (p : Pattern) : 0 ≤ d6577 p :=
  nonnegative_ite (p 163) (nonnegative6576 p) (nonnegative6567 p)
def d6578 (p : Pattern) : Int := if p 162 then d6577 p else d6567 p
theorem agree6578 (p q : Pattern) (h : Agree support p q) : d6578 p = d6578 q := by
  simp only [d6578, h 162 (by decide), agree6577 p q h, agree6567 p q h]
theorem nonnegative6578 (p : Pattern) : 0 ≤ d6578 p :=
  nonnegative_ite (p 162) (nonnegative6577 p) (nonnegative6567 p)
def d6579 (p : Pattern) : Int := if p 225 then d3244 p else d9 p
theorem agree6579 (p q : Pattern) (h : Agree support p q) : d6579 p = d6579 q := by
  simp only [d6579, h 225 (by decide), agree3244 p q h, agree9 p q h]
theorem nonnegative6579 (p : Pattern) : 0 ≤ d6579 p :=
  nonnegative_ite (p 225) (nonnegative3244 p) (nonnegative9 p)
def d6580 (p : Pattern) : Int := if p 224 then d3244 p else d6579 p
theorem agree6580 (p q : Pattern) (h : Agree support p q) : d6580 p = d6580 q := by
  simp only [d6580, h 224 (by decide), agree3244 p q h, agree6579 p q h]
theorem nonnegative6580 (p : Pattern) : 0 ≤ d6580 p :=
  nonnegative_ite (p 224) (nonnegative3244 p) (nonnegative6579 p)
def d6581 (p : Pattern) : Int := if p 204 then d6580 p else d9 p
theorem agree6581 (p q : Pattern) (h : Agree support p q) : d6581 p = d6581 q := by
  simp only [d6581, h 204 (by decide), agree6580 p q h, agree9 p q h]
theorem nonnegative6581 (p : Pattern) : 0 ≤ d6581 p :=
  nonnegative_ite (p 204) (nonnegative6580 p) (nonnegative9 p)
def d6582 (p : Pattern) : Int := if p 246 then d11 p else d9 p
theorem agree6582 (p q : Pattern) (h : Agree support p q) : d6582 p = d6582 q := by
  simp only [d6582, h 246 (by decide), agree11 p q h, agree9 p q h]
theorem nonnegative6582 (p : Pattern) : 0 ≤ d6582 p :=
  nonnegative_ite (p 246) (nonnegative11 p) (nonnegative9 p)
def d6583 (p : Pattern) : Int := if p 225 then d6582 p else d9 p
theorem agree6583 (p q : Pattern) (h : Agree support p q) : d6583 p = d6583 q := by
  simp only [d6583, h 225 (by decide), agree6582 p q h, agree9 p q h]
theorem nonnegative6583 (p : Pattern) : 0 ≤ d6583 p :=
  nonnegative_ite (p 225) (nonnegative6582 p) (nonnegative9 p)
def d6584 (p : Pattern) : Int := if p 224 then d6582 p else d6583 p
theorem agree6584 (p q : Pattern) (h : Agree support p q) : d6584 p = d6584 q := by
  simp only [d6584, h 224 (by decide), agree6582 p q h, agree6583 p q h]
theorem nonnegative6584 (p : Pattern) : 0 ≤ d6584 p :=
  nonnegative_ite (p 224) (nonnegative6582 p) (nonnegative6583 p)
def d6585 (p : Pattern) : Int := if p 204 then d12 p else d6584 p
theorem agree6585 (p q : Pattern) (h : Agree support p q) : d6585 p = d6585 q := by
  simp only [d6585, h 204 (by decide), agree12 p q h, agree6584 p q h]
theorem nonnegative6585 (p : Pattern) : 0 ≤ d6585 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6584 p)
def d6586 (p : Pattern) : Int := if p 182 then d6585 p else d6581 p
theorem agree6586 (p q : Pattern) (h : Agree support p q) : d6586 p = d6586 q := by
  simp only [d6586, h 182 (by decide), agree6585 p q h, agree6581 p q h]
theorem nonnegative6586 (p : Pattern) : 0 ≤ d6586 p :=
  nonnegative_ite (p 182) (nonnegative6585 p) (nonnegative6581 p)
def d6587 (p : Pattern) : Int := if p 163 then d12 p else d6586 p
theorem agree6587 (p q : Pattern) (h : Agree support p q) : d6587 p = d6587 q := by
  simp only [d6587, h 163 (by decide), agree12 p q h, agree6586 p q h]
theorem nonnegative6587 (p : Pattern) : 0 ≤ d6587 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6586 p)
def d6588 (p : Pattern) : Int := if p 162 then d6587 p else d6577 p
theorem agree6588 (p q : Pattern) (h : Agree support p q) : d6588 p = d6588 q := by
  simp only [d6588, h 162 (by decide), agree6587 p q h, agree6577 p q h]
theorem nonnegative6588 (p : Pattern) : 0 ≤ d6588 p :=
  nonnegative_ite (p 162) (nonnegative6587 p) (nonnegative6577 p)
def d6589 (p : Pattern) : Int := if p 161 then d6588 p else d6578 p
theorem agree6589 (p q : Pattern) (h : Agree support p q) : d6589 p = d6589 q := by
  simp only [d6589, h 161 (by decide), agree6588 p q h, agree6578 p q h]
theorem nonnegative6589 (p : Pattern) : 0 ≤ d6589 p :=
  nonnegative_ite (p 161) (nonnegative6588 p) (nonnegative6578 p)
def d6590 (p : Pattern) : Int := if p 246 then d6 p else d0 p
theorem agree6590 (p q : Pattern) (h : Agree support p q) : d6590 p = d6590 q := by
  simp only [d6590, h 246 (by decide), agree6 p q h, agree0 p q h]
theorem nonnegative6590 (p : Pattern) : 0 ≤ d6590 p :=
  nonnegative_ite (p 246) (nonnegative6 p) (nonnegative0 p)
def d6591 (p : Pattern) : Int := if p 225 then d6590 p else d0 p
theorem agree6591 (p q : Pattern) (h : Agree support p q) : d6591 p = d6591 q := by
  simp only [d6591, h 225 (by decide), agree6590 p q h, agree0 p q h]
theorem nonnegative6591 (p : Pattern) : 0 ≤ d6591 p :=
  nonnegative_ite (p 225) (nonnegative6590 p) (nonnegative0 p)
def d6592 (p : Pattern) : Int := if p 246 then d9 p else d0 p
theorem agree6592 (p q : Pattern) (h : Agree support p q) : d6592 p = d6592 q := by
  simp only [d6592, h 246 (by decide), agree9 p q h, agree0 p q h]
theorem nonnegative6592 (p : Pattern) : 0 ≤ d6592 p :=
  nonnegative_ite (p 246) (nonnegative9 p) (nonnegative0 p)
def d6593 (p : Pattern) : Int := if p 225 then d6592 p else d6559 p
theorem agree6593 (p q : Pattern) (h : Agree support p q) : d6593 p = d6593 q := by
  simp only [d6593, h 225 (by decide), agree6592 p q h, agree6559 p q h]
theorem nonnegative6593 (p : Pattern) : 0 ≤ d6593 p :=
  nonnegative_ite (p 225) (nonnegative6592 p) (nonnegative6559 p)
def d6594 (p : Pattern) : Int := if p 224 then d6593 p else d6591 p
theorem agree6594 (p q : Pattern) (h : Agree support p q) : d6594 p = d6594 q := by
  simp only [d6594, h 224 (by decide), agree6593 p q h, agree6591 p q h]
theorem nonnegative6594 (p : Pattern) : 0 ≤ d6594 p :=
  nonnegative_ite (p 224) (nonnegative6593 p) (nonnegative6591 p)
def d6595 (p : Pattern) : Int := if p 204 then d6594 p else d0 p
theorem agree6595 (p q : Pattern) (h : Agree support p q) : d6595 p = d6595 q := by
  simp only [d6595, h 204 (by decide), agree6594 p q h, agree0 p q h]
theorem nonnegative6595 (p : Pattern) : 0 ≤ d6595 p :=
  nonnegative_ite (p 204) (nonnegative6594 p) (nonnegative0 p)
def d6596 (p : Pattern) : Int := if p 246 then d8 p else d2 p
theorem agree6596 (p q : Pattern) (h : Agree support p q) : d6596 p = d6596 q := by
  simp only [d6596, h 246 (by decide), agree8 p q h, agree2 p q h]
theorem nonnegative6596 (p : Pattern) : 0 ≤ d6596 p :=
  nonnegative_ite (p 246) (nonnegative8 p) (nonnegative2 p)
def d6597 (p : Pattern) : Int := if p 225 then d6596 p else d2 p
theorem agree6597 (p q : Pattern) (h : Agree support p q) : d6597 p = d6597 q := by
  simp only [d6597, h 225 (by decide), agree6596 p q h, agree2 p q h]
theorem nonnegative6597 (p : Pattern) : 0 ≤ d6597 p :=
  nonnegative_ite (p 225) (nonnegative6596 p) (nonnegative2 p)
def d6598 (p : Pattern) : Int := if p 246 then d6 p else d2 p
theorem agree6598 (p q : Pattern) (h : Agree support p q) : d6598 p = d6598 q := by
  simp only [d6598, h 246 (by decide), agree6 p q h, agree2 p q h]
theorem nonnegative6598 (p : Pattern) : 0 ≤ d6598 p :=
  nonnegative_ite (p 246) (nonnegative6 p) (nonnegative2 p)
def d6599 (p : Pattern) : Int := if p 246 then d11 p else d2 p
theorem agree6599 (p q : Pattern) (h : Agree support p q) : d6599 p = d6599 q := by
  simp only [d6599, h 246 (by decide), agree11 p q h, agree2 p q h]
theorem nonnegative6599 (p : Pattern) : 0 ≤ d6599 p :=
  nonnegative_ite (p 246) (nonnegative11 p) (nonnegative2 p)
end NetHack.Sokoban22Refined85
