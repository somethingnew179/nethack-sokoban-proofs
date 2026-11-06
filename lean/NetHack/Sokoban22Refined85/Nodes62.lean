/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes61
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d7440 (p : Pattern) : Int := if p 162 then d7439 p else d7438 p
theorem agree7440 (p q : Pattern) (h : Agree support p q) : d7440 p = d7440 q := by
  simp only [d7440, h 162 (by decide), agree7439 p q h, agree7438 p q h]
theorem nonnegative7440 (p : Pattern) : 0 ≤ d7440 p :=
  nonnegative_ite (p 162) (nonnegative7439 p) (nonnegative7438 p)
def d7441 (p : Pattern) : Int := if p 163 then d7320 p else d7401 p
theorem agree7441 (p q : Pattern) (h : Agree support p q) : d7441 p = d7441 q := by
  simp only [d7441, h 163 (by decide), agree7320 p q h, agree7401 p q h]
theorem nonnegative7441 (p : Pattern) : 0 ≤ d7441 p :=
  nonnegative_ite (p 163) (nonnegative7320 p) (nonnegative7401 p)
def d7442 (p : Pattern) : Int := if p 162 then d12 p else d7441 p
theorem agree7442 (p q : Pattern) (h : Agree support p q) : d7442 p = d7442 q := by
  simp only [d7442, h 162 (by decide), agree12 p q h, agree7441 p q h]
theorem nonnegative7442 (p : Pattern) : 0 ≤ d7442 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7441 p)
def d7443 (p : Pattern) : Int := if p 161 then d7442 p else d7440 p
theorem agree7443 (p q : Pattern) (h : Agree support p q) : d7443 p = d7443 q := by
  simp only [d7443, h 161 (by decide), agree7442 p q h, agree7440 p q h]
theorem nonnegative7443 (p : Pattern) : 0 ≤ d7443 p :=
  nonnegative_ite (p 161) (nonnegative7442 p) (nonnegative7440 p)
def d7444 (p : Pattern) : Int := if p 204 then d7413 p else d3 p
theorem agree7444 (p q : Pattern) (h : Agree support p q) : d7444 p = d7444 q := by
  simp only [d7444, h 204 (by decide), agree7413 p q h, agree3 p q h]
theorem nonnegative7444 (p : Pattern) : 0 ≤ d7444 p :=
  nonnegative_ite (p 204) (nonnegative7413 p) (nonnegative3 p)
def d7445 (p : Pattern) : Int := if p 182 then d12 p else d7444 p
theorem agree7445 (p q : Pattern) (h : Agree support p q) : d7445 p = d7445 q := by
  simp only [d7445, h 182 (by decide), agree12 p q h, agree7444 p q h]
theorem nonnegative7445 (p : Pattern) : 0 ≤ d7445 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7444 p)
def d7446 (p : Pattern) : Int := if p 163 then d7445 p else d7418 p
theorem agree7446 (p q : Pattern) (h : Agree support p q) : d7446 p = d7446 q := by
  simp only [d7446, h 163 (by decide), agree7445 p q h, agree7418 p q h]
theorem nonnegative7446 (p : Pattern) : 0 ≤ d7446 p :=
  nonnegative_ite (p 163) (nonnegative7445 p) (nonnegative7418 p)
def d7447 (p : Pattern) : Int := if p 163 then d7329 p else d7424 p
theorem agree7447 (p q : Pattern) (h : Agree support p q) : d7447 p = d7447 q := by
  simp only [d7447, h 163 (by decide), agree7329 p q h, agree7424 p q h]
theorem nonnegative7447 (p : Pattern) : 0 ≤ d7447 p :=
  nonnegative_ite (p 163) (nonnegative7329 p) (nonnegative7424 p)
def d7448 (p : Pattern) : Int := if p 162 then d7447 p else d7446 p
theorem agree7448 (p q : Pattern) (h : Agree support p q) : d7448 p = d7448 q := by
  simp only [d7448, h 162 (by decide), agree7447 p q h, agree7446 p q h]
theorem nonnegative7448 (p : Pattern) : 0 ≤ d7448 p :=
  nonnegative_ite (p 162) (nonnegative7447 p) (nonnegative7446 p)
def d7449 (p : Pattern) : Int := if p 163 then d7331 p else d7424 p
theorem agree7449 (p q : Pattern) (h : Agree support p q) : d7449 p = d7449 q := by
  simp only [d7449, h 163 (by decide), agree7331 p q h, agree7424 p q h]
theorem nonnegative7449 (p : Pattern) : 0 ≤ d7449 p :=
  nonnegative_ite (p 163) (nonnegative7331 p) (nonnegative7424 p)
def d7450 (p : Pattern) : Int := if p 162 then d12 p else d7449 p
theorem agree7450 (p q : Pattern) (h : Agree support p q) : d7450 p = d7450 q := by
  simp only [d7450, h 162 (by decide), agree12 p q h, agree7449 p q h]
theorem nonnegative7450 (p : Pattern) : 0 ≤ d7450 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7449 p)
def d7451 (p : Pattern) : Int := if p 161 then d7450 p else d7448 p
theorem agree7451 (p q : Pattern) (h : Agree support p q) : d7451 p = d7451 q := by
  simp only [d7451, h 161 (by decide), agree7450 p q h, agree7448 p q h]
theorem nonnegative7451 (p : Pattern) : 0 ≤ d7451 p :=
  nonnegative_ite (p 161) (nonnegative7450 p) (nonnegative7448 p)
def d7452 (p : Pattern) : Int := if p 160 then d7451 p else d7443 p
theorem agree7452 (p q : Pattern) (h : Agree support p q) : d7452 p = d7452 q := by
  simp only [d7452, h 160 (by decide), agree7451 p q h, agree7443 p q h]
theorem nonnegative7452 (p : Pattern) : 0 ≤ d7452 p :=
  nonnegative_ite (p 160) (nonnegative7451 p) (nonnegative7443 p)
def d7453 (p : Pattern) : Int := if p 141 then d7452 p else d7430 p
theorem agree7453 (p q : Pattern) (h : Agree support p q) : d7453 p = d7453 q := by
  simp only [d7453, h 141 (by decide), agree7452 p q h, agree7430 p q h]
theorem nonnegative7453 (p : Pattern) : 0 ≤ d7453 p :=
  nonnegative_ite (p 141) (nonnegative7452 p) (nonnegative7430 p)
def d7454 (p : Pattern) : Int := if p 224 then d7398 p else d7407 p
theorem agree7454 (p q : Pattern) (h : Agree support p q) : d7454 p = d7454 q := by
  simp only [d7454, h 224 (by decide), agree7398 p q h, agree7407 p q h]
theorem nonnegative7454 (p : Pattern) : 0 ≤ d7454 p :=
  nonnegative_ite (p 224) (nonnegative7398 p) (nonnegative7407 p)
def d7455 (p : Pattern) : Int := if p 204 then d7454 p else d1 p
theorem agree7455 (p q : Pattern) (h : Agree support p q) : d7455 p = d7455 q := by
  simp only [d7455, h 204 (by decide), agree7454 p q h, agree1 p q h]
theorem nonnegative7455 (p : Pattern) : 0 ≤ d7455 p :=
  nonnegative_ite (p 204) (nonnegative7454 p) (nonnegative1 p)
def d7456 (p : Pattern) : Int := if p 204 then d12 p else d7389 p
theorem agree7456 (p q : Pattern) (h : Agree support p q) : d7456 p = d7456 q := by
  simp only [d7456, h 204 (by decide), agree12 p q h, agree7389 p q h]
theorem nonnegative7456 (p : Pattern) : 0 ≤ d7456 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7389 p)
def d7457 (p : Pattern) : Int := if p 182 then d7456 p else d7455 p
theorem agree7457 (p q : Pattern) (h : Agree support p q) : d7457 p = d7457 q := by
  simp only [d7457, h 182 (by decide), agree7456 p q h, agree7455 p q h]
theorem nonnegative7457 (p : Pattern) : 0 ≤ d7457 p :=
  nonnegative_ite (p 182) (nonnegative7456 p) (nonnegative7455 p)
def d7458 (p : Pattern) : Int := if p 224 then d7395 p else d7407 p
theorem agree7458 (p q : Pattern) (h : Agree support p q) : d7458 p = d7458 q := by
  simp only [d7458, h 224 (by decide), agree7395 p q h, agree7407 p q h]
theorem nonnegative7458 (p : Pattern) : 0 ≤ d7458 p :=
  nonnegative_ite (p 224) (nonnegative7395 p) (nonnegative7407 p)
def d7459 (p : Pattern) : Int := if p 204 then d12 p else d7458 p
theorem agree7459 (p q : Pattern) (h : Agree support p q) : d7459 p = d7459 q := by
  simp only [d7459, h 204 (by decide), agree12 p q h, agree7458 p q h]
theorem nonnegative7459 (p : Pattern) : 0 ≤ d7459 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7458 p)
def d7460 (p : Pattern) : Int := if p 182 then d7459 p else d7410 p
theorem agree7460 (p q : Pattern) (h : Agree support p q) : d7460 p = d7460 q := by
  simp only [d7460, h 182 (by decide), agree7459 p q h, agree7410 p q h]
theorem nonnegative7460 (p : Pattern) : 0 ≤ d7460 p :=
  nonnegative_ite (p 182) (nonnegative7459 p) (nonnegative7410 p)
def d7461 (p : Pattern) : Int := if p 163 then d7460 p else d7457 p
theorem agree7461 (p q : Pattern) (h : Agree support p q) : d7461 p = d7461 q := by
  simp only [d7461, h 163 (by decide), agree7460 p q h, agree7457 p q h]
theorem nonnegative7461 (p : Pattern) : 0 ≤ d7461 p :=
  nonnegative_ite (p 163) (nonnegative7460 p) (nonnegative7457 p)
def d7462 (p : Pattern) : Int := if p 204 then d12 p else d7409 p
theorem agree7462 (p q : Pattern) (h : Agree support p q) : d7462 p = d7462 q := by
  simp only [d7462, h 204 (by decide), agree12 p q h, agree7409 p q h]
theorem nonnegative7462 (p : Pattern) : 0 ≤ d7462 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7409 p)
def d7463 (p : Pattern) : Int := if p 182 then d7462 p else d7410 p
theorem agree7463 (p q : Pattern) (h : Agree support p q) : d7463 p = d7463 q := by
  simp only [d7463, h 182 (by decide), agree7462 p q h, agree7410 p q h]
theorem nonnegative7463 (p : Pattern) : 0 ≤ d7463 p :=
  nonnegative_ite (p 182) (nonnegative7462 p) (nonnegative7410 p)
def d7464 (p : Pattern) : Int := if p 204 then d12 p else d7422 p
theorem agree7464 (p q : Pattern) (h : Agree support p q) : d7464 p = d7464 q := by
  simp only [d7464, h 204 (by decide), agree12 p q h, agree7422 p q h]
theorem nonnegative7464 (p : Pattern) : 0 ≤ d7464 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7422 p)
def d7465 (p : Pattern) : Int := if p 182 then d7464 p else d7423 p
theorem agree7465 (p q : Pattern) (h : Agree support p q) : d7465 p = d7465 q := by
  simp only [d7465, h 182 (by decide), agree7464 p q h, agree7423 p q h]
theorem nonnegative7465 (p : Pattern) : 0 ≤ d7465 p :=
  nonnegative_ite (p 182) (nonnegative7464 p) (nonnegative7423 p)
def d7466 (p : Pattern) : Int := if p 163 then d7465 p else d7463 p
theorem agree7466 (p q : Pattern) (h : Agree support p q) : d7466 p = d7466 q := by
  simp only [d7466, h 163 (by decide), agree7465 p q h, agree7463 p q h]
theorem nonnegative7466 (p : Pattern) : 0 ≤ d7466 p :=
  nonnegative_ite (p 163) (nonnegative7465 p) (nonnegative7463 p)
def d7467 (p : Pattern) : Int := if p 162 then d7466 p else d7461 p
theorem agree7467 (p q : Pattern) (h : Agree support p q) : d7467 p = d7467 q := by
  simp only [d7467, h 162 (by decide), agree7466 p q h, agree7461 p q h]
theorem nonnegative7467 (p : Pattern) : 0 ≤ d7467 p :=
  nonnegative_ite (p 162) (nonnegative7466 p) (nonnegative7461 p)
def d7468 (p : Pattern) : Int := if p 162 then d7404 p else d7466 p
theorem agree7468 (p q : Pattern) (h : Agree support p q) : d7468 p = d7468 q := by
  simp only [d7468, h 162 (by decide), agree7404 p q h, agree7466 p q h]
theorem nonnegative7468 (p : Pattern) : 0 ≤ d7468 p :=
  nonnegative_ite (p 162) (nonnegative7404 p) (nonnegative7466 p)
def d7469 (p : Pattern) : Int := if p 161 then d7468 p else d7467 p
theorem agree7469 (p q : Pattern) (h : Agree support p q) : d7469 p = d7469 q := by
  simp only [d7469, h 161 (by decide), agree7468 p q h, agree7467 p q h]
theorem nonnegative7469 (p : Pattern) : 0 ≤ d7469 p :=
  nonnegative_ite (p 161) (nonnegative7468 p) (nonnegative7467 p)
def d7470 (p : Pattern) : Int := if p 182 then d7414 p else d7444 p
theorem agree7470 (p q : Pattern) (h : Agree support p q) : d7470 p = d7470 q := by
  simp only [d7470, h 182 (by decide), agree7414 p q h, agree7444 p q h]
theorem nonnegative7470 (p : Pattern) : 0 ≤ d7470 p :=
  nonnegative_ite (p 182) (nonnegative7414 p) (nonnegative7444 p)
def d7471 (p : Pattern) : Int := if p 204 then d7416 p else d7 p
theorem agree7471 (p q : Pattern) (h : Agree support p q) : d7471 p = d7471 q := by
  simp only [d7471, h 204 (by decide), agree7416 p q h, agree7 p q h]
theorem nonnegative7471 (p : Pattern) : 0 ≤ d7471 p :=
  nonnegative_ite (p 204) (nonnegative7416 p) (nonnegative7 p)
def d7472 (p : Pattern) : Int := if p 182 then d7417 p else d7471 p
theorem agree7472 (p q : Pattern) (h : Agree support p q) : d7472 p = d7472 q := by
  simp only [d7472, h 182 (by decide), agree7417 p q h, agree7471 p q h]
theorem nonnegative7472 (p : Pattern) : 0 ≤ d7472 p :=
  nonnegative_ite (p 182) (nonnegative7417 p) (nonnegative7471 p)
def d7473 (p : Pattern) : Int := if p 163 then d7472 p else d7470 p
theorem agree7473 (p q : Pattern) (h : Agree support p q) : d7473 p = d7473 q := by
  simp only [d7473, h 163 (by decide), agree7472 p q h, agree7470 p q h]
theorem nonnegative7473 (p : Pattern) : 0 ≤ d7473 p :=
  nonnegative_ite (p 163) (nonnegative7472 p) (nonnegative7470 p)
def d7474 (p : Pattern) : Int := if p 162 then d12 p else d7473 p
theorem agree7474 (p q : Pattern) (h : Agree support p q) : d7474 p = d7474 q := by
  simp only [d7474, h 162 (by decide), agree12 p q h, agree7473 p q h]
theorem nonnegative7474 (p : Pattern) : 0 ≤ d7474 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7473 p)
def d7475 (p : Pattern) : Int := if p 161 then d12 p else d7474 p
theorem agree7475 (p q : Pattern) (h : Agree support p q) : d7475 p = d7475 q := by
  simp only [d7475, h 161 (by decide), agree12 p q h, agree7474 p q h]
theorem nonnegative7475 (p : Pattern) : 0 ≤ d7475 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7474 p)
def d7476 (p : Pattern) : Int := if p 160 then d7475 p else d7469 p
theorem agree7476 (p q : Pattern) (h : Agree support p q) : d7476 p = d7476 q := by
  simp only [d7476, h 160 (by decide), agree7475 p q h, agree7469 p q h]
theorem nonnegative7476 (p : Pattern) : 0 ≤ d7476 p :=
  nonnegative_ite (p 160) (nonnegative7475 p) (nonnegative7469 p)
def d7477 (p : Pattern) : Int := if p 163 then d7470 p else d7460 p
theorem agree7477 (p q : Pattern) (h : Agree support p q) : d7477 p = d7477 q := by
  simp only [d7477, h 163 (by decide), agree7470 p q h, agree7460 p q h]
theorem nonnegative7477 (p : Pattern) : 0 ≤ d7477 p :=
  nonnegative_ite (p 163) (nonnegative7470 p) (nonnegative7460 p)
def d7478 (p : Pattern) : Int := if p 163 then d7317 p else d7465 p
theorem agree7478 (p q : Pattern) (h : Agree support p q) : d7478 p = d7478 q := by
  simp only [d7478, h 163 (by decide), agree7317 p q h, agree7465 p q h]
theorem nonnegative7478 (p : Pattern) : 0 ≤ d7478 p :=
  nonnegative_ite (p 163) (nonnegative7317 p) (nonnegative7465 p)
def d7479 (p : Pattern) : Int := if p 162 then d7478 p else d7477 p
theorem agree7479 (p q : Pattern) (h : Agree support p q) : d7479 p = d7479 q := by
  simp only [d7479, h 162 (by decide), agree7478 p q h, agree7477 p q h]
theorem nonnegative7479 (p : Pattern) : 0 ≤ d7479 p :=
  nonnegative_ite (p 162) (nonnegative7478 p) (nonnegative7477 p)
def d7480 (p : Pattern) : Int := if p 163 then d7320 p else d7465 p
theorem agree7480 (p q : Pattern) (h : Agree support p q) : d7480 p = d7480 q := by
  simp only [d7480, h 163 (by decide), agree7320 p q h, agree7465 p q h]
theorem nonnegative7480 (p : Pattern) : 0 ≤ d7480 p :=
  nonnegative_ite (p 163) (nonnegative7320 p) (nonnegative7465 p)
def d7481 (p : Pattern) : Int := if p 162 then d12 p else d7480 p
theorem agree7481 (p q : Pattern) (h : Agree support p q) : d7481 p = d7481 q := by
  simp only [d7481, h 162 (by decide), agree12 p q h, agree7480 p q h]
theorem nonnegative7481 (p : Pattern) : 0 ≤ d7481 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7480 p)
def d7482 (p : Pattern) : Int := if p 161 then d7481 p else d7479 p
theorem agree7482 (p q : Pattern) (h : Agree support p q) : d7482 p = d7482 q := by
  simp only [d7482, h 161 (by decide), agree7481 p q h, agree7479 p q h]
theorem nonnegative7482 (p : Pattern) : 0 ≤ d7482 p :=
  nonnegative_ite (p 161) (nonnegative7481 p) (nonnegative7479 p)
def d7483 (p : Pattern) : Int := if p 163 then d12 p else d7472 p
theorem agree7483 (p q : Pattern) (h : Agree support p q) : d7483 p = d7483 q := by
  simp only [d7483, h 163 (by decide), agree12 p q h, agree7472 p q h]
theorem nonnegative7483 (p : Pattern) : 0 ≤ d7483 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7472 p)
def d7484 (p : Pattern) : Int := if p 162 then d12 p else d7483 p
theorem agree7484 (p q : Pattern) (h : Agree support p q) : d7484 p = d7484 q := by
  simp only [d7484, h 162 (by decide), agree12 p q h, agree7483 p q h]
theorem nonnegative7484 (p : Pattern) : 0 ≤ d7484 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7483 p)
def d7485 (p : Pattern) : Int := if p 161 then d12 p else d7484 p
theorem agree7485 (p q : Pattern) (h : Agree support p q) : d7485 p = d7485 q := by
  simp only [d7485, h 161 (by decide), agree12 p q h, agree7484 p q h]
theorem nonnegative7485 (p : Pattern) : 0 ≤ d7485 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7484 p)
def d7486 (p : Pattern) : Int := if p 160 then d7485 p else d7482 p
theorem agree7486 (p q : Pattern) (h : Agree support p q) : d7486 p = d7486 q := by
  simp only [d7486, h 160 (by decide), agree7485 p q h, agree7482 p q h]
theorem nonnegative7486 (p : Pattern) : 0 ≤ d7486 p :=
  nonnegative_ite (p 160) (nonnegative7485 p) (nonnegative7482 p)
def d7487 (p : Pattern) : Int := if p 141 then d7486 p else d7476 p
theorem agree7487 (p q : Pattern) (h : Agree support p q) : d7487 p = d7487 q := by
  simp only [d7487, h 141 (by decide), agree7486 p q h, agree7476 p q h]
theorem nonnegative7487 (p : Pattern) : 0 ≤ d7487 p :=
  nonnegative_ite (p 141) (nonnegative7486 p) (nonnegative7476 p)
def d7488 (p : Pattern) : Int := if p 138 then d7487 p else d7453 p
theorem agree7488 (p q : Pattern) (h : Agree support p q) : d7488 p = d7488 q := by
  simp only [d7488, h 138 (by decide), agree7487 p q h, agree7453 p q h]
theorem nonnegative7488 (p : Pattern) : 0 ≤ d7488 p :=
  nonnegative_ite (p 138) (nonnegative7487 p) (nonnegative7453 p)
def d7489 (p : Pattern) : Int := if p 162 then d12 p else d7404 p
theorem agree7489 (p q : Pattern) (h : Agree support p q) : d7489 p = d7489 q := by
  simp only [d7489, h 162 (by decide), agree12 p q h, agree7404 p q h]
theorem nonnegative7489 (p : Pattern) : 0 ≤ d7489 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7404 p)
def d7490 (p : Pattern) : Int := if p 161 then d12 p else d7489 p
theorem agree7490 (p q : Pattern) (h : Agree support p q) : d7490 p = d7490 q := by
  simp only [d7490, h 161 (by decide), agree12 p q h, agree7489 p q h]
theorem nonnegative7490 (p : Pattern) : 0 ≤ d7490 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7489 p)
def d7491 (p : Pattern) : Int := if p 160 then d12 p else d7490 p
theorem agree7491 (p q : Pattern) (h : Agree support p q) : d7491 p = d7491 q := by
  simp only [d7491, h 160 (by decide), agree12 p q h, agree7490 p q h]
theorem nonnegative7491 (p : Pattern) : 0 ≤ d7491 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative7490 p)
def d7492 (p : Pattern) : Int := if p 141 then d12 p else d7491 p
theorem agree7492 (p q : Pattern) (h : Agree support p q) : d7492 p = d7492 q := by
  simp only [d7492, h 141 (by decide), agree12 p q h, agree7491 p q h]
theorem nonnegative7492 (p : Pattern) : 0 ≤ d7492 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative7491 p)
def d7493 (p : Pattern) : Int := if p 138 then d7492 p else d7487 p
theorem agree7493 (p q : Pattern) (h : Agree support p q) : d7493 p = d7493 q := by
  simp only [d7493, h 138 (by decide), agree7492 p q h, agree7487 p q h]
theorem nonnegative7493 (p : Pattern) : 0 ≤ d7493 p :=
  nonnegative_ite (p 138) (nonnegative7492 p) (nonnegative7487 p)
def d7494 (p : Pattern) : Int := if p 116 then d7493 p else d7488 p
theorem agree7494 (p q : Pattern) (h : Agree support p q) : d7494 p = d7494 q := by
  simp only [d7494, h 116 (by decide), agree7493 p q h, agree7488 p q h]
theorem nonnegative7494 (p : Pattern) : 0 ≤ d7494 p :=
  nonnegative_ite (p 116) (nonnegative7493 p) (nonnegative7488 p)
def d7495 (p : Pattern) : Int := if p 138 then d12 p else d7487 p
theorem agree7495 (p q : Pattern) (h : Agree support p q) : d7495 p = d7495 q := by
  simp only [d7495, h 138 (by decide), agree12 p q h, agree7487 p q h]
theorem nonnegative7495 (p : Pattern) : 0 ≤ d7495 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7487 p)
def d7496 (p : Pattern) : Int := if p 116 then d7495 p else d7488 p
theorem agree7496 (p q : Pattern) (h : Agree support p q) : d7496 p = d7496 q := by
  simp only [d7496, h 116 (by decide), agree7495 p q h, agree7488 p q h]
theorem nonnegative7496 (p : Pattern) : 0 ≤ d7496 p :=
  nonnegative_ite (p 116) (nonnegative7495 p) (nonnegative7488 p)
def d7497 (p : Pattern) : Int := if p 115 then d7496 p else d7494 p
theorem agree7497 (p q : Pattern) (h : Agree support p q) : d7497 p = d7497 q := by
  simp only [d7497, h 115 (by decide), agree7496 p q h, agree7494 p q h]
theorem nonnegative7497 (p : Pattern) : 0 ≤ d7497 p :=
  nonnegative_ite (p 115) (nonnegative7496 p) (nonnegative7494 p)
def d7498 (p : Pattern) : Int := if p 71 then d7497 p else d7387 p
theorem agree7498 (p q : Pattern) (h : Agree support p q) : d7498 p = d7498 q := by
  simp only [d7498, h 71 (by decide), agree7497 p q h, agree7387 p q h]
theorem nonnegative7498 (p : Pattern) : 0 ≤ d7498 p :=
  nonnegative_ite (p 71) (nonnegative7497 p) (nonnegative7387 p)
def d7499 (p : Pattern) : Int := if p 49 then d7498 p else d7387 p
theorem agree7499 (p q : Pattern) (h : Agree support p q) : d7499 p = d7499 q := by
  simp only [d7499, h 49 (by decide), agree7498 p q h, agree7387 p q h]
theorem nonnegative7499 (p : Pattern) : 0 ≤ d7499 p :=
  nonnegative_ite (p 49) (nonnegative7498 p) (nonnegative7387 p)
def d7500 (p : Pattern) : Int := if p 225 then d10 p else d8 p
theorem agree7500 (p q : Pattern) (h : Agree support p q) : d7500 p = d7500 q := by
  simp only [d7500, h 225 (by decide), agree10 p q h, agree8 p q h]
theorem nonnegative7500 (p : Pattern) : 0 ≤ d7500 p :=
  nonnegative_ite (p 225) (nonnegative10 p) (nonnegative8 p)
def d7501 (p : Pattern) : Int := if p 224 then d7500 p else d7290 p
theorem agree7501 (p q : Pattern) (h : Agree support p q) : d7501 p = d7501 q := by
  simp only [d7501, h 224 (by decide), agree7500 p q h, agree7290 p q h]
theorem nonnegative7501 (p : Pattern) : 0 ≤ d7501 p :=
  nonnegative_ite (p 224) (nonnegative7500 p) (nonnegative7290 p)
def d7502 (p : Pattern) : Int := if p 204 then d7501 p else d4 p
theorem agree7502 (p q : Pattern) (h : Agree support p q) : d7502 p = d7502 q := by
  simp only [d7502, h 204 (by decide), agree7501 p q h, agree4 p q h]
theorem nonnegative7502 (p : Pattern) : 0 ≤ d7502 p :=
  nonnegative_ite (p 204) (nonnegative7501 p) (nonnegative4 p)
def d7503 (p : Pattern) : Int := if p 204 then d12 p else d7253 p
theorem agree7503 (p q : Pattern) (h : Agree support p q) : d7503 p = d7503 q := by
  simp only [d7503, h 204 (by decide), agree12 p q h, agree7253 p q h]
theorem nonnegative7503 (p : Pattern) : 0 ≤ d7503 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7253 p)
def d7504 (p : Pattern) : Int := if p 182 then d7503 p else d7502 p
theorem agree7504 (p q : Pattern) (h : Agree support p q) : d7504 p = d7504 q := by
  simp only [d7504, h 182 (by decide), agree7503 p q h, agree7502 p q h]
theorem nonnegative7504 (p : Pattern) : 0 ≤ d7504 p :=
  nonnegative_ite (p 182) (nonnegative7503 p) (nonnegative7502 p)
def d7505 (p : Pattern) : Int := if p 163 then d7504 p else d7340 p
theorem agree7505 (p q : Pattern) (h : Agree support p q) : d7505 p = d7505 q := by
  simp only [d7505, h 163 (by decide), agree7504 p q h, agree7340 p q h]
theorem nonnegative7505 (p : Pattern) : 0 ≤ d7505 p :=
  nonnegative_ite (p 163) (nonnegative7504 p) (nonnegative7340 p)
def d7506 (p : Pattern) : Int := if p 162 then d7505 p else d7340 p
theorem agree7506 (p q : Pattern) (h : Agree support p q) : d7506 p = d7506 q := by
  simp only [d7506, h 162 (by decide), agree7505 p q h, agree7340 p q h]
theorem nonnegative7506 (p : Pattern) : 0 ≤ d7506 p :=
  nonnegative_ite (p 162) (nonnegative7505 p) (nonnegative7340 p)
def d7507 (p : Pattern) : Int := if p 162 then d7353 p else d7505 p
theorem agree7507 (p q : Pattern) (h : Agree support p q) : d7507 p = d7507 q := by
  simp only [d7507, h 162 (by decide), agree7353 p q h, agree7505 p q h]
theorem nonnegative7507 (p : Pattern) : 0 ≤ d7507 p :=
  nonnegative_ite (p 162) (nonnegative7353 p) (nonnegative7505 p)
def d7508 (p : Pattern) : Int := if p 161 then d7507 p else d7506 p
theorem agree7508 (p q : Pattern) (h : Agree support p q) : d7508 p = d7508 q := by
  simp only [d7508, h 161 (by decide), agree7507 p q h, agree7506 p q h]
theorem nonnegative7508 (p : Pattern) : 0 ≤ d7508 p :=
  nonnegative_ite (p 161) (nonnegative7507 p) (nonnegative7506 p)
def d7509 (p : Pattern) : Int := if p 182 then d7283 p else d7324 p
theorem agree7509 (p q : Pattern) (h : Agree support p q) : d7509 p = d7509 q := by
  simp only [d7509, h 182 (by decide), agree7283 p q h, agree7324 p q h]
theorem nonnegative7509 (p : Pattern) : 0 ≤ d7509 p :=
  nonnegative_ite (p 182) (nonnegative7283 p) (nonnegative7324 p)
def d7510 (p : Pattern) : Int := if p 163 then d7509 p else d7356 p
theorem agree7510 (p q : Pattern) (h : Agree support p q) : d7510 p = d7510 q := by
  simp only [d7510, h 163 (by decide), agree7509 p q h, agree7356 p q h]
theorem nonnegative7510 (p : Pattern) : 0 ≤ d7510 p :=
  nonnegative_ite (p 163) (nonnegative7509 p) (nonnegative7356 p)
def d7511 (p : Pattern) : Int := if p 182 then d7288 p else d7324 p
theorem agree7511 (p q : Pattern) (h : Agree support p q) : d7511 p = d7511 q := by
  simp only [d7511, h 182 (by decide), agree7288 p q h, agree7324 p q h]
theorem nonnegative7511 (p : Pattern) : 0 ≤ d7511 p :=
  nonnegative_ite (p 182) (nonnegative7288 p) (nonnegative7324 p)
def d7512 (p : Pattern) : Int := if p 182 then d12 p else d7357 p
theorem agree7512 (p q : Pattern) (h : Agree support p q) : d7512 p = d7512 q := by
  simp only [d7512, h 182 (by decide), agree12 p q h, agree7357 p q h]
theorem nonnegative7512 (p : Pattern) : 0 ≤ d7512 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7357 p)
def d7513 (p : Pattern) : Int := if p 163 then d7512 p else d7511 p
theorem agree7513 (p q : Pattern) (h : Agree support p q) : d7513 p = d7513 q := by
  simp only [d7513, h 163 (by decide), agree7512 p q h, agree7511 p q h]
theorem nonnegative7513 (p : Pattern) : 0 ≤ d7513 p :=
  nonnegative_ite (p 163) (nonnegative7512 p) (nonnegative7511 p)
def d7514 (p : Pattern) : Int := if p 162 then d7513 p else d7510 p
theorem agree7514 (p q : Pattern) (h : Agree support p q) : d7514 p = d7514 q := by
  simp only [d7514, h 162 (by decide), agree7513 p q h, agree7510 p q h]
theorem nonnegative7514 (p : Pattern) : 0 ≤ d7514 p :=
  nonnegative_ite (p 162) (nonnegative7513 p) (nonnegative7510 p)
def d7515 (p : Pattern) : Int := if p 163 then d7512 p else d7325 p
theorem agree7515 (p q : Pattern) (h : Agree support p q) : d7515 p = d7515 q := by
  simp only [d7515, h 163 (by decide), agree7512 p q h, agree7325 p q h]
theorem nonnegative7515 (p : Pattern) : 0 ≤ d7515 p :=
  nonnegative_ite (p 163) (nonnegative7512 p) (nonnegative7325 p)
def d7516 (p : Pattern) : Int := if p 162 then d7332 p else d7515 p
theorem agree7516 (p q : Pattern) (h : Agree support p q) : d7516 p = d7516 q := by
  simp only [d7516, h 162 (by decide), agree7332 p q h, agree7515 p q h]
theorem nonnegative7516 (p : Pattern) : 0 ≤ d7516 p :=
  nonnegative_ite (p 162) (nonnegative7332 p) (nonnegative7515 p)
def d7517 (p : Pattern) : Int := if p 161 then d7516 p else d7514 p
theorem agree7517 (p q : Pattern) (h : Agree support p q) : d7517 p = d7517 q := by
  simp only [d7517, h 161 (by decide), agree7516 p q h, agree7514 p q h]
theorem nonnegative7517 (p : Pattern) : 0 ≤ d7517 p :=
  nonnegative_ite (p 161) (nonnegative7516 p) (nonnegative7514 p)
def d7518 (p : Pattern) : Int := if p 160 then d7517 p else d7508 p
theorem agree7518 (p q : Pattern) (h : Agree support p q) : d7518 p = d7518 q := by
  simp only [d7518, h 160 (by decide), agree7517 p q h, agree7508 p q h]
theorem nonnegative7518 (p : Pattern) : 0 ≤ d7518 p :=
  nonnegative_ite (p 160) (nonnegative7517 p) (nonnegative7508 p)
def d7519 (p : Pattern) : Int := if p 225 then d8 p else d6 p
theorem agree7519 (p q : Pattern) (h : Agree support p q) : d7519 p = d7519 q := by
  simp only [d7519, h 225 (by decide), agree8 p q h, agree6 p q h]
theorem nonnegative7519 (p : Pattern) : 0 ≤ d7519 p :=
  nonnegative_ite (p 225) (nonnegative8 p) (nonnegative6 p)
def d7520 (p : Pattern) : Int := if p 224 then d7519 p else d7275 p
theorem agree7520 (p q : Pattern) (h : Agree support p q) : d7520 p = d7520 q := by
  simp only [d7520, h 224 (by decide), agree7519 p q h, agree7275 p q h]
theorem nonnegative7520 (p : Pattern) : 0 ≤ d7520 p :=
  nonnegative_ite (p 224) (nonnegative7519 p) (nonnegative7275 p)
def d7521 (p : Pattern) : Int := if p 204 then d7520 p else d2 p
theorem agree7521 (p q : Pattern) (h : Agree support p q) : d7521 p = d7521 q := by
  simp only [d7521, h 204 (by decide), agree7520 p q h, agree2 p q h]
theorem nonnegative7521 (p : Pattern) : 0 ≤ d7521 p :=
  nonnegative_ite (p 204) (nonnegative7520 p) (nonnegative2 p)
def d7522 (p : Pattern) : Int := if p 204 then d12 p else d7305 p
theorem agree7522 (p q : Pattern) (h : Agree support p q) : d7522 p = d7522 q := by
  simp only [d7522, h 204 (by decide), agree12 p q h, agree7305 p q h]
theorem nonnegative7522 (p : Pattern) : 0 ≤ d7522 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7305 p)
def d7523 (p : Pattern) : Int := if p 182 then d7522 p else d7521 p
theorem agree7523 (p q : Pattern) (h : Agree support p q) : d7523 p = d7523 q := by
  simp only [d7523, h 182 (by decide), agree7522 p q h, agree7521 p q h]
theorem nonnegative7523 (p : Pattern) : 0 ≤ d7523 p :=
  nonnegative_ite (p 182) (nonnegative7522 p) (nonnegative7521 p)
def d7524 (p : Pattern) : Int := if p 163 then d7523 p else d7340 p
theorem agree7524 (p q : Pattern) (h : Agree support p q) : d7524 p = d7524 q := by
  simp only [d7524, h 163 (by decide), agree7523 p q h, agree7340 p q h]
theorem nonnegative7524 (p : Pattern) : 0 ≤ d7524 p :=
  nonnegative_ite (p 163) (nonnegative7523 p) (nonnegative7340 p)
def d7525 (p : Pattern) : Int := if p 163 then d7352 p else d7504 p
theorem agree7525 (p q : Pattern) (h : Agree support p q) : d7525 p = d7525 q := by
  simp only [d7525, h 163 (by decide), agree7352 p q h, agree7504 p q h]
theorem nonnegative7525 (p : Pattern) : 0 ≤ d7525 p :=
  nonnegative_ite (p 163) (nonnegative7352 p) (nonnegative7504 p)
def d7526 (p : Pattern) : Int := if p 162 then d7525 p else d7524 p
theorem agree7526 (p q : Pattern) (h : Agree support p q) : d7526 p = d7526 q := by
  simp only [d7526, h 162 (by decide), agree7525 p q h, agree7524 p q h]
theorem nonnegative7526 (p : Pattern) : 0 ≤ d7526 p :=
  nonnegative_ite (p 162) (nonnegative7525 p) (nonnegative7524 p)
def d7527 (p : Pattern) : Int := if p 163 then d7317 p else d7504 p
theorem agree7527 (p q : Pattern) (h : Agree support p q) : d7527 p = d7527 q := by
  simp only [d7527, h 163 (by decide), agree7317 p q h, agree7504 p q h]
theorem nonnegative7527 (p : Pattern) : 0 ≤ d7527 p :=
  nonnegative_ite (p 163) (nonnegative7317 p) (nonnegative7504 p)
def d7528 (p : Pattern) : Int := if p 162 then d7321 p else d7527 p
theorem agree7528 (p q : Pattern) (h : Agree support p q) : d7528 p = d7528 q := by
  simp only [d7528, h 162 (by decide), agree7321 p q h, agree7527 p q h]
theorem nonnegative7528 (p : Pattern) : 0 ≤ d7528 p :=
  nonnegative_ite (p 162) (nonnegative7321 p) (nonnegative7527 p)
def d7529 (p : Pattern) : Int := if p 161 then d7528 p else d7526 p
theorem agree7529 (p q : Pattern) (h : Agree support p q) : d7529 p = d7529 q := by
  simp only [d7529, h 161 (by decide), agree7528 p q h, agree7526 p q h]
theorem nonnegative7529 (p : Pattern) : 0 ≤ d7529 p :=
  nonnegative_ite (p 161) (nonnegative7528 p) (nonnegative7526 p)
def d7530 (p : Pattern) : Int := if p 163 then d7294 p else d7509 p
theorem agree7530 (p q : Pattern) (h : Agree support p q) : d7530 p = d7530 q := by
  simp only [d7530, h 163 (by decide), agree7294 p q h, agree7509 p q h]
theorem nonnegative7530 (p : Pattern) : 0 ≤ d7530 p :=
  nonnegative_ite (p 163) (nonnegative7294 p) (nonnegative7509 p)
def d7531 (p : Pattern) : Int := if p 163 then d7331 p else d7512 p
theorem agree7531 (p q : Pattern) (h : Agree support p q) : d7531 p = d7531 q := by
  simp only [d7531, h 163 (by decide), agree7331 p q h, agree7512 p q h]
theorem nonnegative7531 (p : Pattern) : 0 ≤ d7531 p :=
  nonnegative_ite (p 163) (nonnegative7331 p) (nonnegative7512 p)
def d7532 (p : Pattern) : Int := if p 162 then d7531 p else d7530 p
theorem agree7532 (p q : Pattern) (h : Agree support p q) : d7532 p = d7532 q := by
  simp only [d7532, h 162 (by decide), agree7531 p q h, agree7530 p q h]
theorem nonnegative7532 (p : Pattern) : 0 ≤ d7532 p :=
  nonnegative_ite (p 162) (nonnegative7531 p) (nonnegative7530 p)
def d7533 (p : Pattern) : Int := if p 163 then d12 p else d7512 p
theorem agree7533 (p q : Pattern) (h : Agree support p q) : d7533 p = d7533 q := by
  simp only [d7533, h 163 (by decide), agree12 p q h, agree7512 p q h]
theorem nonnegative7533 (p : Pattern) : 0 ≤ d7533 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7512 p)
def d7534 (p : Pattern) : Int := if p 162 then d12 p else d7533 p
theorem agree7534 (p q : Pattern) (h : Agree support p q) : d7534 p = d7534 q := by
  simp only [d7534, h 162 (by decide), agree12 p q h, agree7533 p q h]
theorem nonnegative7534 (p : Pattern) : 0 ≤ d7534 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7533 p)
def d7535 (p : Pattern) : Int := if p 161 then d7534 p else d7532 p
theorem agree7535 (p q : Pattern) (h : Agree support p q) : d7535 p = d7535 q := by
  simp only [d7535, h 161 (by decide), agree7534 p q h, agree7532 p q h]
theorem nonnegative7535 (p : Pattern) : 0 ≤ d7535 p :=
  nonnegative_ite (p 161) (nonnegative7534 p) (nonnegative7532 p)
def d7536 (p : Pattern) : Int := if p 160 then d7535 p else d7529 p
theorem agree7536 (p q : Pattern) (h : Agree support p q) : d7536 p = d7536 q := by
  simp only [d7536, h 160 (by decide), agree7535 p q h, agree7529 p q h]
theorem nonnegative7536 (p : Pattern) : 0 ≤ d7536 p :=
  nonnegative_ite (p 160) (nonnegative7535 p) (nonnegative7529 p)
def d7537 (p : Pattern) : Int := if p 141 then d7536 p else d7518 p
theorem agree7537 (p q : Pattern) (h : Agree support p q) : d7537 p = d7537 q := by
  simp only [d7537, h 141 (by decide), agree7536 p q h, agree7518 p q h]
theorem nonnegative7537 (p : Pattern) : 0 ≤ d7537 p :=
  nonnegative_ite (p 141) (nonnegative7536 p) (nonnegative7518 p)
def d7538 (p : Pattern) : Int := if p 204 then d7341 p else d0 p
theorem agree7538 (p q : Pattern) (h : Agree support p q) : d7538 p = d7538 q := by
  simp only [d7538, h 204 (by decide), agree7341 p q h, agree0 p q h]
theorem nonnegative7538 (p : Pattern) : 0 ≤ d7538 p :=
  nonnegative_ite (p 204) (nonnegative7341 p) (nonnegative0 p)
def d7539 (p : Pattern) : Int := if p 204 then d12 p else d7337 p
theorem agree7539 (p q : Pattern) (h : Agree support p q) : d7539 p = d7539 q := by
  simp only [d7539, h 204 (by decide), agree12 p q h, agree7337 p q h]
theorem nonnegative7539 (p : Pattern) : 0 ≤ d7539 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7337 p)
def d7540 (p : Pattern) : Int := if p 182 then d7539 p else d7538 p
theorem agree7540 (p q : Pattern) (h : Agree support p q) : d7540 p = d7540 q := by
  simp only [d7540, h 182 (by decide), agree7539 p q h, agree7538 p q h]
theorem nonnegative7540 (p : Pattern) : 0 ≤ d7540 p :=
  nonnegative_ite (p 182) (nonnegative7539 p) (nonnegative7538 p)
def d7541 (p : Pattern) : Int := if p 163 then d7346 p else d7540 p
theorem agree7541 (p q : Pattern) (h : Agree support p q) : d7541 p = d7541 q := by
  simp only [d7541, h 163 (by decide), agree7346 p q h, agree7540 p q h]
theorem nonnegative7541 (p : Pattern) : 0 ≤ d7541 p :=
  nonnegative_ite (p 163) (nonnegative7346 p) (nonnegative7540 p)
def d7542 (p : Pattern) : Int := if p 162 then d7359 p else d7541 p
theorem agree7542 (p q : Pattern) (h : Agree support p q) : d7542 p = d7542 q := by
  simp only [d7542, h 162 (by decide), agree7359 p q h, agree7541 p q h]
theorem nonnegative7542 (p : Pattern) : 0 ≤ d7542 p :=
  nonnegative_ite (p 162) (nonnegative7359 p) (nonnegative7541 p)
def d7543 (p : Pattern) : Int := if p 161 then d7360 p else d7542 p
theorem agree7543 (p q : Pattern) (h : Agree support p q) : d7543 p = d7543 q := by
  simp only [d7543, h 161 (by decide), agree7360 p q h, agree7542 p q h]
theorem nonnegative7543 (p : Pattern) : 0 ≤ d7543 p :=
  nonnegative_ite (p 161) (nonnegative7360 p) (nonnegative7542 p)
def d7544 (p : Pattern) : Int := if p 224 then d12 p else d7291 p
theorem agree7544 (p q : Pattern) (h : Agree support p q) : d7544 p = d7544 q := by
  simp only [d7544, h 224 (by decide), agree12 p q h, agree7291 p q h]
theorem nonnegative7544 (p : Pattern) : 0 ≤ d7544 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative7291 p)
def d7545 (p : Pattern) : Int := if p 204 then d7544 p else d8 p
theorem agree7545 (p q : Pattern) (h : Agree support p q) : d7545 p = d7545 q := by
  simp only [d7545, h 204 (by decide), agree7544 p q h, agree8 p q h]
theorem nonnegative7545 (p : Pattern) : 0 ≤ d7545 p :=
  nonnegative_ite (p 204) (nonnegative7544 p) (nonnegative8 p)
def d7546 (p : Pattern) : Int := if p 204 then d12 p else d7544 p
theorem agree7546 (p q : Pattern) (h : Agree support p q) : d7546 p = d7546 q := by
  simp only [d7546, h 204 (by decide), agree12 p q h, agree7544 p q h]
theorem nonnegative7546 (p : Pattern) : 0 ≤ d7546 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7544 p)
def d7547 (p : Pattern) : Int := if p 182 then d7546 p else d7545 p
theorem agree7547 (p q : Pattern) (h : Agree support p q) : d7547 p = d7547 q := by
  simp only [d7547, h 182 (by decide), agree7546 p q h, agree7545 p q h]
theorem nonnegative7547 (p : Pattern) : 0 ≤ d7547 p :=
  nonnegative_ite (p 182) (nonnegative7546 p) (nonnegative7545 p)
def d7548 (p : Pattern) : Int := if p 163 then d7547 p else d7348 p
theorem agree7548 (p q : Pattern) (h : Agree support p q) : d7548 p = d7548 q := by
  simp only [d7548, h 163 (by decide), agree7547 p q h, agree7348 p q h]
theorem nonnegative7548 (p : Pattern) : 0 ≤ d7548 p :=
  nonnegative_ite (p 163) (nonnegative7547 p) (nonnegative7348 p)
def d7549 (p : Pattern) : Int := if p 162 then d12 p else d7548 p
theorem agree7549 (p q : Pattern) (h : Agree support p q) : d7549 p = d7549 q := by
  simp only [d7549, h 162 (by decide), agree12 p q h, agree7548 p q h]
theorem nonnegative7549 (p : Pattern) : 0 ≤ d7549 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7548 p)
def d7550 (p : Pattern) : Int := if p 161 then d12 p else d7549 p
theorem agree7550 (p q : Pattern) (h : Agree support p q) : d7550 p = d7550 q := by
  simp only [d7550, h 161 (by decide), agree12 p q h, agree7549 p q h]
theorem nonnegative7550 (p : Pattern) : 0 ≤ d7550 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7549 p)
def d7551 (p : Pattern) : Int := if p 160 then d7550 p else d7543 p
theorem agree7551 (p q : Pattern) (h : Agree support p q) : d7551 p = d7551 q := by
  simp only [d7551, h 160 (by decide), agree7550 p q h, agree7543 p q h]
theorem nonnegative7551 (p : Pattern) : 0 ≤ d7551 p :=
  nonnegative_ite (p 160) (nonnegative7550 p) (nonnegative7543 p)
def d7552 (p : Pattern) : Int := if p 225 then d10 p else d6 p
theorem agree7552 (p q : Pattern) (h : Agree support p q) : d7552 p = d7552 q := by
  simp only [d7552, h 225 (by decide), agree10 p q h, agree6 p q h]
theorem nonnegative7552 (p : Pattern) : 0 ≤ d7552 p :=
  nonnegative_ite (p 225) (nonnegative10 p) (nonnegative6 p)
def d7553 (p : Pattern) : Int := if p 224 then d7552 p else d7275 p
theorem agree7553 (p q : Pattern) (h : Agree support p q) : d7553 p = d7553 q := by
  simp only [d7553, h 224 (by decide), agree7552 p q h, agree7275 p q h]
theorem nonnegative7553 (p : Pattern) : 0 ≤ d7553 p :=
  nonnegative_ite (p 224) (nonnegative7552 p) (nonnegative7275 p)
def d7554 (p : Pattern) : Int := if p 204 then d12 p else d7553 p
theorem agree7554 (p q : Pattern) (h : Agree support p q) : d7554 p = d7554 q := by
  simp only [d7554, h 204 (by decide), agree12 p q h, agree7553 p q h]
theorem nonnegative7554 (p : Pattern) : 0 ≤ d7554 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7553 p)
def d7555 (p : Pattern) : Int := if p 182 then d7554 p else d7324 p
theorem agree7555 (p q : Pattern) (h : Agree support p q) : d7555 p = d7555 q := by
  simp only [d7555, h 182 (by decide), agree7554 p q h, agree7324 p q h]
theorem nonnegative7555 (p : Pattern) : 0 ≤ d7555 p :=
  nonnegative_ite (p 182) (nonnegative7554 p) (nonnegative7324 p)
def d7556 (p : Pattern) : Int := if p 163 then d7356 p else d7555 p
theorem agree7556 (p q : Pattern) (h : Agree support p q) : d7556 p = d7556 q := by
  simp only [d7556, h 163 (by decide), agree7356 p q h, agree7555 p q h]
theorem nonnegative7556 (p : Pattern) : 0 ≤ d7556 p :=
  nonnegative_ite (p 163) (nonnegative7356 p) (nonnegative7555 p)
def d7557 (p : Pattern) : Int := if p 163 then d7320 p else d7348 p
theorem agree7557 (p q : Pattern) (h : Agree support p q) : d7557 p = d7557 q := by
  simp only [d7557, h 163 (by decide), agree7320 p q h, agree7348 p q h]
theorem nonnegative7557 (p : Pattern) : 0 ≤ d7557 p :=
  nonnegative_ite (p 163) (nonnegative7320 p) (nonnegative7348 p)
def d7558 (p : Pattern) : Int := if p 162 then d7557 p else d7556 p
theorem agree7558 (p q : Pattern) (h : Agree support p q) : d7558 p = d7558 q := by
  simp only [d7558, h 162 (by decide), agree7557 p q h, agree7556 p q h]
theorem nonnegative7558 (p : Pattern) : 0 ≤ d7558 p :=
  nonnegative_ite (p 162) (nonnegative7557 p) (nonnegative7556 p)
def d7559 (p : Pattern) : Int := if p 161 then d7370 p else d7558 p
theorem agree7559 (p q : Pattern) (h : Agree support p q) : d7559 p = d7559 q := by
  simp only [d7559, h 161 (by decide), agree7370 p q h, agree7558 p q h]
theorem nonnegative7559 (p : Pattern) : 0 ≤ d7559 p :=
  nonnegative_ite (p 161) (nonnegative7370 p) (nonnegative7558 p)
end NetHack.Sokoban22Refined85
