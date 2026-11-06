/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes62
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d7560 (p : Pattern) : Int := if p 163 then d12 p else d7547 p
theorem agree7560 (p q : Pattern) (h : Agree support p q) : d7560 p = d7560 q := by
  simp only [d7560, h 163 (by decide), agree12 p q h, agree7547 p q h]
theorem nonnegative7560 (p : Pattern) : 0 ≤ d7560 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7547 p)
def d7561 (p : Pattern) : Int := if p 162 then d12 p else d7560 p
theorem agree7561 (p q : Pattern) (h : Agree support p q) : d7561 p = d7561 q := by
  simp only [d7561, h 162 (by decide), agree12 p q h, agree7560 p q h]
theorem nonnegative7561 (p : Pattern) : 0 ≤ d7561 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7560 p)
def d7562 (p : Pattern) : Int := if p 161 then d12 p else d7561 p
theorem agree7562 (p q : Pattern) (h : Agree support p q) : d7562 p = d7562 q := by
  simp only [d7562, h 161 (by decide), agree12 p q h, agree7561 p q h]
theorem nonnegative7562 (p : Pattern) : 0 ≤ d7562 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7561 p)
def d7563 (p : Pattern) : Int := if p 160 then d7562 p else d7559 p
theorem agree7563 (p q : Pattern) (h : Agree support p q) : d7563 p = d7563 q := by
  simp only [d7563, h 160 (by decide), agree7562 p q h, agree7559 p q h]
theorem nonnegative7563 (p : Pattern) : 0 ≤ d7563 p :=
  nonnegative_ite (p 160) (nonnegative7562 p) (nonnegative7559 p)
def d7564 (p : Pattern) : Int := if p 141 then d7563 p else d7551 p
theorem agree7564 (p q : Pattern) (h : Agree support p q) : d7564 p = d7564 q := by
  simp only [d7564, h 141 (by decide), agree7563 p q h, agree7551 p q h]
theorem nonnegative7564 (p : Pattern) : 0 ≤ d7564 p :=
  nonnegative_ite (p 141) (nonnegative7563 p) (nonnegative7551 p)
def d7565 (p : Pattern) : Int := if p 138 then d7564 p else d7537 p
theorem agree7565 (p q : Pattern) (h : Agree support p q) : d7565 p = d7565 q := by
  simp only [d7565, h 138 (by decide), agree7564 p q h, agree7537 p q h]
theorem nonnegative7565 (p : Pattern) : 0 ≤ d7565 p :=
  nonnegative_ite (p 138) (nonnegative7564 p) (nonnegative7537 p)
def d7566 (p : Pattern) : Int := if p 138 then d12 p else d7564 p
theorem agree7566 (p q : Pattern) (h : Agree support p q) : d7566 p = d7566 q := by
  simp only [d7566, h 138 (by decide), agree12 p q h, agree7564 p q h]
theorem nonnegative7566 (p : Pattern) : 0 ≤ d7566 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7564 p)
def d7567 (p : Pattern) : Int := if p 116 then d7566 p else d7565 p
theorem agree7567 (p q : Pattern) (h : Agree support p q) : d7567 p = d7567 q := by
  simp only [d7567, h 116 (by decide), agree7566 p q h, agree7565 p q h]
theorem nonnegative7567 (p : Pattern) : 0 ≤ d7567 p :=
  nonnegative_ite (p 116) (nonnegative7566 p) (nonnegative7565 p)
def d7568 (p : Pattern) : Int := if p 115 then d7567 p else d7384 p
theorem agree7568 (p q : Pattern) (h : Agree support p q) : d7568 p = d7568 q := by
  simp only [d7568, h 115 (by decide), agree7567 p q h, agree7384 p q h]
theorem nonnegative7568 (p : Pattern) : 0 ≤ d7568 p :=
  nonnegative_ite (p 115) (nonnegative7567 p) (nonnegative7384 p)
def d7569 (p : Pattern) : Int := if p 71 then d7568 p else d7387 p
theorem agree7569 (p q : Pattern) (h : Agree support p q) : d7569 p = d7569 q := by
  simp only [d7569, h 71 (by decide), agree7568 p q h, agree7387 p q h]
theorem nonnegative7569 (p : Pattern) : 0 ≤ d7569 p :=
  nonnegative_ite (p 71) (nonnegative7568 p) (nonnegative7387 p)
def d7570 (p : Pattern) : Int := if p 163 then d12 p else d7401 p
theorem agree7570 (p q : Pattern) (h : Agree support p q) : d7570 p = d7570 q := by
  simp only [d7570, h 163 (by decide), agree12 p q h, agree7401 p q h]
theorem nonnegative7570 (p : Pattern) : 0 ≤ d7570 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7401 p)
def d7571 (p : Pattern) : Int := if p 162 then d7570 p else d7438 p
theorem agree7571 (p q : Pattern) (h : Agree support p q) : d7571 p = d7571 q := by
  simp only [d7571, h 162 (by decide), agree7570 p q h, agree7438 p q h]
theorem nonnegative7571 (p : Pattern) : 0 ≤ d7571 p :=
  nonnegative_ite (p 162) (nonnegative7570 p) (nonnegative7438 p)
def d7572 (p : Pattern) : Int := if p 162 then d12 p else d7570 p
theorem agree7572 (p q : Pattern) (h : Agree support p q) : d7572 p = d7572 q := by
  simp only [d7572, h 162 (by decide), agree12 p q h, agree7570 p q h]
theorem nonnegative7572 (p : Pattern) : 0 ≤ d7572 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7570 p)
def d7573 (p : Pattern) : Int := if p 161 then d7572 p else d7571 p
theorem agree7573 (p q : Pattern) (h : Agree support p q) : d7573 p = d7573 q := by
  simp only [d7573, h 161 (by decide), agree7572 p q h, agree7571 p q h]
theorem nonnegative7573 (p : Pattern) : 0 ≤ d7573 p :=
  nonnegative_ite (p 161) (nonnegative7572 p) (nonnegative7571 p)
def d7574 (p : Pattern) : Int := if p 163 then d12 p else d7424 p
theorem agree7574 (p q : Pattern) (h : Agree support p q) : d7574 p = d7574 q := by
  simp only [d7574, h 163 (by decide), agree12 p q h, agree7424 p q h]
theorem nonnegative7574 (p : Pattern) : 0 ≤ d7574 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7424 p)
def d7575 (p : Pattern) : Int := if p 162 then d7574 p else d7446 p
theorem agree7575 (p q : Pattern) (h : Agree support p q) : d7575 p = d7575 q := by
  simp only [d7575, h 162 (by decide), agree7574 p q h, agree7446 p q h]
theorem nonnegative7575 (p : Pattern) : 0 ≤ d7575 p :=
  nonnegative_ite (p 162) (nonnegative7574 p) (nonnegative7446 p)
def d7576 (p : Pattern) : Int := if p 162 then d12 p else d7574 p
theorem agree7576 (p q : Pattern) (h : Agree support p q) : d7576 p = d7576 q := by
  simp only [d7576, h 162 (by decide), agree12 p q h, agree7574 p q h]
theorem nonnegative7576 (p : Pattern) : 0 ≤ d7576 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7574 p)
def d7577 (p : Pattern) : Int := if p 161 then d7576 p else d7575 p
theorem agree7577 (p q : Pattern) (h : Agree support p q) : d7577 p = d7577 q := by
  simp only [d7577, h 161 (by decide), agree7576 p q h, agree7575 p q h]
theorem nonnegative7577 (p : Pattern) : 0 ≤ d7577 p :=
  nonnegative_ite (p 161) (nonnegative7576 p) (nonnegative7575 p)
def d7578 (p : Pattern) : Int := if p 160 then d7577 p else d7573 p
theorem agree7578 (p q : Pattern) (h : Agree support p q) : d7578 p = d7578 q := by
  simp only [d7578, h 160 (by decide), agree7577 p q h, agree7573 p q h]
theorem nonnegative7578 (p : Pattern) : 0 ≤ d7578 p :=
  nonnegative_ite (p 160) (nonnegative7577 p) (nonnegative7573 p)
def d7579 (p : Pattern) : Int := if p 141 then d7578 p else d7430 p
theorem agree7579 (p q : Pattern) (h : Agree support p q) : d7579 p = d7579 q := by
  simp only [d7579, h 141 (by decide), agree7578 p q h, agree7430 p q h]
theorem nonnegative7579 (p : Pattern) : 0 ≤ d7579 p :=
  nonnegative_ite (p 141) (nonnegative7578 p) (nonnegative7430 p)
def d7580 (p : Pattern) : Int := if p 163 then d12 p else d7465 p
theorem agree7580 (p q : Pattern) (h : Agree support p q) : d7580 p = d7580 q := by
  simp only [d7580, h 163 (by decide), agree12 p q h, agree7465 p q h]
theorem nonnegative7580 (p : Pattern) : 0 ≤ d7580 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7465 p)
def d7581 (p : Pattern) : Int := if p 162 then d7580 p else d7477 p
theorem agree7581 (p q : Pattern) (h : Agree support p q) : d7581 p = d7581 q := by
  simp only [d7581, h 162 (by decide), agree7580 p q h, agree7477 p q h]
theorem nonnegative7581 (p : Pattern) : 0 ≤ d7581 p :=
  nonnegative_ite (p 162) (nonnegative7580 p) (nonnegative7477 p)
def d7582 (p : Pattern) : Int := if p 162 then d12 p else d7580 p
theorem agree7582 (p q : Pattern) (h : Agree support p q) : d7582 p = d7582 q := by
  simp only [d7582, h 162 (by decide), agree12 p q h, agree7580 p q h]
theorem nonnegative7582 (p : Pattern) : 0 ≤ d7582 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7580 p)
def d7583 (p : Pattern) : Int := if p 161 then d7582 p else d7581 p
theorem agree7583 (p q : Pattern) (h : Agree support p q) : d7583 p = d7583 q := by
  simp only [d7583, h 161 (by decide), agree7582 p q h, agree7581 p q h]
theorem nonnegative7583 (p : Pattern) : 0 ≤ d7583 p :=
  nonnegative_ite (p 161) (nonnegative7582 p) (nonnegative7581 p)
def d7584 (p : Pattern) : Int := if p 160 then d7485 p else d7583 p
theorem agree7584 (p q : Pattern) (h : Agree support p q) : d7584 p = d7584 q := by
  simp only [d7584, h 160 (by decide), agree7485 p q h, agree7583 p q h]
theorem nonnegative7584 (p : Pattern) : 0 ≤ d7584 p :=
  nonnegative_ite (p 160) (nonnegative7485 p) (nonnegative7583 p)
def d7585 (p : Pattern) : Int := if p 141 then d7584 p else d7476 p
theorem agree7585 (p q : Pattern) (h : Agree support p q) : d7585 p = d7585 q := by
  simp only [d7585, h 141 (by decide), agree7584 p q h, agree7476 p q h]
theorem nonnegative7585 (p : Pattern) : 0 ≤ d7585 p :=
  nonnegative_ite (p 141) (nonnegative7584 p) (nonnegative7476 p)
def d7586 (p : Pattern) : Int := if p 138 then d7585 p else d7579 p
theorem agree7586 (p q : Pattern) (h : Agree support p q) : d7586 p = d7586 q := by
  simp only [d7586, h 138 (by decide), agree7585 p q h, agree7579 p q h]
theorem nonnegative7586 (p : Pattern) : 0 ≤ d7586 p :=
  nonnegative_ite (p 138) (nonnegative7585 p) (nonnegative7579 p)
def d7587 (p : Pattern) : Int := if p 138 then d7492 p else d7585 p
theorem agree7587 (p q : Pattern) (h : Agree support p q) : d7587 p = d7587 q := by
  simp only [d7587, h 138 (by decide), agree7492 p q h, agree7585 p q h]
theorem nonnegative7587 (p : Pattern) : 0 ≤ d7587 p :=
  nonnegative_ite (p 138) (nonnegative7492 p) (nonnegative7585 p)
def d7588 (p : Pattern) : Int := if p 116 then d7587 p else d7586 p
theorem agree7588 (p q : Pattern) (h : Agree support p q) : d7588 p = d7588 q := by
  simp only [d7588, h 116 (by decide), agree7587 p q h, agree7586 p q h]
theorem nonnegative7588 (p : Pattern) : 0 ≤ d7588 p :=
  nonnegative_ite (p 116) (nonnegative7587 p) (nonnegative7586 p)
def d7589 (p : Pattern) : Int := if p 204 then d7458 p else d1 p
theorem agree7589 (p q : Pattern) (h : Agree support p q) : d7589 p = d7589 q := by
  simp only [d7589, h 204 (by decide), agree7458 p q h, agree1 p q h]
theorem nonnegative7589 (p : Pattern) : 0 ≤ d7589 p :=
  nonnegative_ite (p 204) (nonnegative7458 p) (nonnegative1 p)
def d7590 (p : Pattern) : Int := if p 204 then d12 p else d7454 p
theorem agree7590 (p q : Pattern) (h : Agree support p q) : d7590 p = d7590 q := by
  simp only [d7590, h 204 (by decide), agree12 p q h, agree7454 p q h]
theorem nonnegative7590 (p : Pattern) : 0 ≤ d7590 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7454 p)
def d7591 (p : Pattern) : Int := if p 182 then d7590 p else d7589 p
theorem agree7591 (p q : Pattern) (h : Agree support p q) : d7591 p = d7591 q := by
  simp only [d7591, h 182 (by decide), agree7590 p q h, agree7589 p q h]
theorem nonnegative7591 (p : Pattern) : 0 ≤ d7591 p :=
  nonnegative_ite (p 182) (nonnegative7590 p) (nonnegative7589 p)
def d7592 (p : Pattern) : Int := if p 163 then d7465 p else d7591 p
theorem agree7592 (p q : Pattern) (h : Agree support p q) : d7592 p = d7592 q := by
  simp only [d7592, h 163 (by decide), agree7465 p q h, agree7591 p q h]
theorem nonnegative7592 (p : Pattern) : 0 ≤ d7592 p :=
  nonnegative_ite (p 163) (nonnegative7465 p) (nonnegative7591 p)
def d7593 (p : Pattern) : Int := if p 162 then d7592 p else d7457 p
theorem agree7593 (p q : Pattern) (h : Agree support p q) : d7593 p = d7593 q := by
  simp only [d7593, h 162 (by decide), agree7592 p q h, agree7457 p q h]
theorem nonnegative7593 (p : Pattern) : 0 ≤ d7593 p :=
  nonnegative_ite (p 162) (nonnegative7592 p) (nonnegative7457 p)
def d7594 (p : Pattern) : Int := if p 163 then d7465 p else d7460 p
theorem agree7594 (p q : Pattern) (h : Agree support p q) : d7594 p = d7594 q := by
  simp only [d7594, h 163 (by decide), agree7465 p q h, agree7460 p q h]
theorem nonnegative7594 (p : Pattern) : 0 ≤ d7594 p :=
  nonnegative_ite (p 163) (nonnegative7465 p) (nonnegative7460 p)
def d7595 (p : Pattern) : Int := if p 162 then d7404 p else d7594 p
theorem agree7595 (p q : Pattern) (h : Agree support p q) : d7595 p = d7595 q := by
  simp only [d7595, h 162 (by decide), agree7404 p q h, agree7594 p q h]
theorem nonnegative7595 (p : Pattern) : 0 ≤ d7595 p :=
  nonnegative_ite (p 162) (nonnegative7404 p) (nonnegative7594 p)
def d7596 (p : Pattern) : Int := if p 161 then d7595 p else d7593 p
theorem agree7596 (p q : Pattern) (h : Agree support p q) : d7596 p = d7596 q := by
  simp only [d7596, h 161 (by decide), agree7595 p q h, agree7593 p q h]
theorem nonnegative7596 (p : Pattern) : 0 ≤ d7596 p :=
  nonnegative_ite (p 161) (nonnegative7595 p) (nonnegative7593 p)
def d7597 (p : Pattern) : Int := if p 182 then d7417 p else d7444 p
theorem agree7597 (p q : Pattern) (h : Agree support p q) : d7597 p = d7597 q := by
  simp only [d7597, h 182 (by decide), agree7417 p q h, agree7444 p q h]
theorem nonnegative7597 (p : Pattern) : 0 ≤ d7597 p :=
  nonnegative_ite (p 182) (nonnegative7417 p) (nonnegative7444 p)
def d7598 (p : Pattern) : Int := if p 163 then d7597 p else d7470 p
theorem agree7598 (p q : Pattern) (h : Agree support p q) : d7598 p = d7598 q := by
  simp only [d7598, h 163 (by decide), agree7597 p q h, agree7470 p q h]
theorem nonnegative7598 (p : Pattern) : 0 ≤ d7598 p :=
  nonnegative_ite (p 163) (nonnegative7597 p) (nonnegative7470 p)
def d7599 (p : Pattern) : Int := if p 162 then d7574 p else d7598 p
theorem agree7599 (p q : Pattern) (h : Agree support p q) : d7599 p = d7599 q := by
  simp only [d7599, h 162 (by decide), agree7574 p q h, agree7598 p q h]
theorem nonnegative7599 (p : Pattern) : 0 ≤ d7599 p :=
  nonnegative_ite (p 162) (nonnegative7574 p) (nonnegative7598 p)
def d7600 (p : Pattern) : Int := if p 182 then d12 p else d7471 p
theorem agree7600 (p q : Pattern) (h : Agree support p q) : d7600 p = d7600 q := by
  simp only [d7600, h 182 (by decide), agree12 p q h, agree7471 p q h]
theorem nonnegative7600 (p : Pattern) : 0 ≤ d7600 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7471 p)
def d7601 (p : Pattern) : Int := if p 163 then d12 p else d7600 p
theorem agree7601 (p q : Pattern) (h : Agree support p q) : d7601 p = d7601 q := by
  simp only [d7601, h 163 (by decide), agree12 p q h, agree7600 p q h]
theorem nonnegative7601 (p : Pattern) : 0 ≤ d7601 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7600 p)
def d7602 (p : Pattern) : Int := if p 162 then d12 p else d7601 p
theorem agree7602 (p q : Pattern) (h : Agree support p q) : d7602 p = d7602 q := by
  simp only [d7602, h 162 (by decide), agree12 p q h, agree7601 p q h]
theorem nonnegative7602 (p : Pattern) : 0 ≤ d7602 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7601 p)
def d7603 (p : Pattern) : Int := if p 161 then d7602 p else d7599 p
theorem agree7603 (p q : Pattern) (h : Agree support p q) : d7603 p = d7603 q := by
  simp only [d7603, h 161 (by decide), agree7602 p q h, agree7599 p q h]
theorem nonnegative7603 (p : Pattern) : 0 ≤ d7603 p :=
  nonnegative_ite (p 161) (nonnegative7602 p) (nonnegative7599 p)
def d7604 (p : Pattern) : Int := if p 160 then d7603 p else d7596 p
theorem agree7604 (p q : Pattern) (h : Agree support p q) : d7604 p = d7604 q := by
  simp only [d7604, h 160 (by decide), agree7603 p q h, agree7596 p q h]
theorem nonnegative7604 (p : Pattern) : 0 ≤ d7604 p :=
  nonnegative_ite (p 160) (nonnegative7603 p) (nonnegative7596 p)
def d7605 (p : Pattern) : Int := if p 225 then d9 p else d7 p
theorem agree7605 (p q : Pattern) (h : Agree support p q) : d7605 p = d7605 q := by
  simp only [d7605, h 225 (by decide), agree9 p q h, agree7 p q h]
theorem nonnegative7605 (p : Pattern) : 0 ≤ d7605 p :=
  nonnegative_ite (p 225) (nonnegative9 p) (nonnegative7 p)
def d7606 (p : Pattern) : Int := if p 224 then d7605 p else d7411 p
theorem agree7606 (p q : Pattern) (h : Agree support p q) : d7606 p = d7606 q := by
  simp only [d7606, h 224 (by decide), agree7605 p q h, agree7411 p q h]
theorem nonnegative7606 (p : Pattern) : 0 ≤ d7606 p :=
  nonnegative_ite (p 224) (nonnegative7605 p) (nonnegative7411 p)
def d7607 (p : Pattern) : Int := if p 204 then d7606 p else d3 p
theorem agree7607 (p q : Pattern) (h : Agree support p q) : d7607 p = d7607 q := by
  simp only [d7607, h 204 (by decide), agree7606 p q h, agree3 p q h]
theorem nonnegative7607 (p : Pattern) : 0 ≤ d7607 p :=
  nonnegative_ite (p 204) (nonnegative7606 p) (nonnegative3 p)
def d7608 (p : Pattern) : Int := if p 204 then d12 p else d7432 p
theorem agree7608 (p q : Pattern) (h : Agree support p q) : d7608 p = d7608 q := by
  simp only [d7608, h 204 (by decide), agree12 p q h, agree7432 p q h]
theorem nonnegative7608 (p : Pattern) : 0 ≤ d7608 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7432 p)
def d7609 (p : Pattern) : Int := if p 182 then d7608 p else d7607 p
theorem agree7609 (p q : Pattern) (h : Agree support p q) : d7609 p = d7609 q := by
  simp only [d7609, h 182 (by decide), agree7608 p q h, agree7607 p q h]
theorem nonnegative7609 (p : Pattern) : 0 ≤ d7609 p :=
  nonnegative_ite (p 182) (nonnegative7608 p) (nonnegative7607 p)
def d7610 (p : Pattern) : Int := if p 163 then d7609 p else d7591 p
theorem agree7610 (p q : Pattern) (h : Agree support p q) : d7610 p = d7610 q := by
  simp only [d7610, h 163 (by decide), agree7609 p q h, agree7591 p q h]
theorem nonnegative7610 (p : Pattern) : 0 ≤ d7610 p :=
  nonnegative_ite (p 163) (nonnegative7609 p) (nonnegative7591 p)
def d7611 (p : Pattern) : Int := if p 224 then d7264 p else d7421 p
theorem agree7611 (p q : Pattern) (h : Agree support p q) : d7611 p = d7611 q := by
  simp only [d7611, h 224 (by decide), agree7264 p q h, agree7421 p q h]
theorem nonnegative7611 (p : Pattern) : 0 ≤ d7611 p :=
  nonnegative_ite (p 224) (nonnegative7264 p) (nonnegative7421 p)
def d7612 (p : Pattern) : Int := if p 204 then d7611 p else d5 p
theorem agree7612 (p q : Pattern) (h : Agree support p q) : d7612 p = d7612 q := by
  simp only [d7612, h 204 (by decide), agree7611 p q h, agree5 p q h]
theorem nonnegative7612 (p : Pattern) : 0 ≤ d7612 p :=
  nonnegative_ite (p 204) (nonnegative7611 p) (nonnegative5 p)
def d7613 (p : Pattern) : Int := if p 204 then d12 p else d7396 p
theorem agree7613 (p q : Pattern) (h : Agree support p q) : d7613 p = d7613 q := by
  simp only [d7613, h 204 (by decide), agree12 p q h, agree7396 p q h]
theorem nonnegative7613 (p : Pattern) : 0 ≤ d7613 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7396 p)
def d7614 (p : Pattern) : Int := if p 182 then d7613 p else d7612 p
theorem agree7614 (p q : Pattern) (h : Agree support p q) : d7614 p = d7614 q := by
  simp only [d7614, h 182 (by decide), agree7613 p q h, agree7612 p q h]
theorem nonnegative7614 (p : Pattern) : 0 ≤ d7614 p :=
  nonnegative_ite (p 182) (nonnegative7613 p) (nonnegative7612 p)
def d7615 (p : Pattern) : Int := if p 163 then d12 p else d7614 p
theorem agree7615 (p q : Pattern) (h : Agree support p q) : d7615 p = d7615 q := by
  simp only [d7615, h 163 (by decide), agree12 p q h, agree7614 p q h]
theorem nonnegative7615 (p : Pattern) : 0 ≤ d7615 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7614 p)
def d7616 (p : Pattern) : Int := if p 162 then d7615 p else d7610 p
theorem agree7616 (p q : Pattern) (h : Agree support p q) : d7616 p = d7616 q := by
  simp only [d7616, h 162 (by decide), agree7615 p q h, agree7610 p q h]
theorem nonnegative7616 (p : Pattern) : 0 ≤ d7616 p :=
  nonnegative_ite (p 162) (nonnegative7615 p) (nonnegative7610 p)
def d7617 (p : Pattern) : Int := if p 204 then d12 p else d7611 p
theorem agree7617 (p q : Pattern) (h : Agree support p q) : d7617 p = d7617 q := by
  simp only [d7617, h 204 (by decide), agree12 p q h, agree7611 p q h]
theorem nonnegative7617 (p : Pattern) : 0 ≤ d7617 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7611 p)
def d7618 (p : Pattern) : Int := if p 182 then d7617 p else d7423 p
theorem agree7618 (p q : Pattern) (h : Agree support p q) : d7618 p = d7618 q := by
  simp only [d7618, h 182 (by decide), agree7617 p q h, agree7423 p q h]
theorem nonnegative7618 (p : Pattern) : 0 ≤ d7618 p :=
  nonnegative_ite (p 182) (nonnegative7617 p) (nonnegative7423 p)
def d7619 (p : Pattern) : Int := if p 163 then d12 p else d7618 p
theorem agree7619 (p q : Pattern) (h : Agree support p q) : d7619 p = d7619 q := by
  simp only [d7619, h 163 (by decide), agree12 p q h, agree7618 p q h]
theorem nonnegative7619 (p : Pattern) : 0 ≤ d7619 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7618 p)
def d7620 (p : Pattern) : Int := if p 162 then d12 p else d7619 p
theorem agree7620 (p q : Pattern) (h : Agree support p q) : d7620 p = d7620 q := by
  simp only [d7620, h 162 (by decide), agree12 p q h, agree7619 p q h]
theorem nonnegative7620 (p : Pattern) : 0 ≤ d7620 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7619 p)
def d7621 (p : Pattern) : Int := if p 161 then d7620 p else d7616 p
theorem agree7621 (p q : Pattern) (h : Agree support p q) : d7621 p = d7621 q := by
  simp only [d7621, h 161 (by decide), agree7620 p q h, agree7616 p q h]
theorem nonnegative7621 (p : Pattern) : 0 ≤ d7621 p :=
  nonnegative_ite (p 161) (nonnegative7620 p) (nonnegative7616 p)
def d7622 (p : Pattern) : Int := if p 182 then d7417 p else d7423 p
theorem agree7622 (p q : Pattern) (h : Agree support p q) : d7622 p = d7622 q := by
  simp only [d7622, h 182 (by decide), agree7417 p q h, agree7423 p q h]
theorem nonnegative7622 (p : Pattern) : 0 ≤ d7622 p :=
  nonnegative_ite (p 182) (nonnegative7417 p) (nonnegative7423 p)
def d7623 (p : Pattern) : Int := if p 163 then d7424 p else d7622 p
theorem agree7623 (p q : Pattern) (h : Agree support p q) : d7623 p = d7623 q := by
  simp only [d7623, h 163 (by decide), agree7424 p q h, agree7622 p q h]
theorem nonnegative7623 (p : Pattern) : 0 ≤ d7623 p :=
  nonnegative_ite (p 163) (nonnegative7424 p) (nonnegative7622 p)
def d7624 (p : Pattern) : Int := if p 162 then d7601 p else d7623 p
theorem agree7624 (p q : Pattern) (h : Agree support p q) : d7624 p = d7624 q := by
  simp only [d7624, h 162 (by decide), agree7601 p q h, agree7623 p q h]
theorem nonnegative7624 (p : Pattern) : 0 ≤ d7624 p :=
  nonnegative_ite (p 162) (nonnegative7601 p) (nonnegative7623 p)
def d7625 (p : Pattern) : Int := if p 162 then d12 p else d7300 p
theorem agree7625 (p q : Pattern) (h : Agree support p q) : d7625 p = d7625 q := by
  simp only [d7625, h 162 (by decide), agree12 p q h, agree7300 p q h]
theorem nonnegative7625 (p : Pattern) : 0 ≤ d7625 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7300 p)
def d7626 (p : Pattern) : Int := if p 161 then d7625 p else d7624 p
theorem agree7626 (p q : Pattern) (h : Agree support p q) : d7626 p = d7626 q := by
  simp only [d7626, h 161 (by decide), agree7625 p q h, agree7624 p q h]
theorem nonnegative7626 (p : Pattern) : 0 ≤ d7626 p :=
  nonnegative_ite (p 161) (nonnegative7625 p) (nonnegative7624 p)
def d7627 (p : Pattern) : Int := if p 160 then d7626 p else d7621 p
theorem agree7627 (p q : Pattern) (h : Agree support p q) : d7627 p = d7627 q := by
  simp only [d7627, h 160 (by decide), agree7626 p q h, agree7621 p q h]
theorem nonnegative7627 (p : Pattern) : 0 ≤ d7627 p :=
  nonnegative_ite (p 160) (nonnegative7626 p) (nonnegative7621 p)
def d7628 (p : Pattern) : Int := if p 141 then d7627 p else d7604 p
theorem agree7628 (p q : Pattern) (h : Agree support p q) : d7628 p = d7628 q := by
  simp only [d7628, h 141 (by decide), agree7627 p q h, agree7604 p q h]
theorem nonnegative7628 (p : Pattern) : 0 ≤ d7628 p :=
  nonnegative_ite (p 141) (nonnegative7627 p) (nonnegative7604 p)
def d7629 (p : Pattern) : Int := if p 163 then d7463 p else d7460 p
theorem agree7629 (p q : Pattern) (h : Agree support p q) : d7629 p = d7629 q := by
  simp only [d7629, h 163 (by decide), agree7463 p q h, agree7460 p q h]
theorem nonnegative7629 (p : Pattern) : 0 ≤ d7629 p :=
  nonnegative_ite (p 163) (nonnegative7463 p) (nonnegative7460 p)
def d7630 (p : Pattern) : Int := if p 163 then d7320 p else d7470 p
theorem agree7630 (p q : Pattern) (h : Agree support p q) : d7630 p = d7630 q := by
  simp only [d7630, h 163 (by decide), agree7320 p q h, agree7470 p q h]
theorem nonnegative7630 (p : Pattern) : 0 ≤ d7630 p :=
  nonnegative_ite (p 163) (nonnegative7320 p) (nonnegative7470 p)
def d7631 (p : Pattern) : Int := if p 162 then d7630 p else d7629 p
theorem agree7631 (p q : Pattern) (h : Agree support p q) : d7631 p = d7631 q := by
  simp only [d7631, h 162 (by decide), agree7630 p q h, agree7629 p q h]
theorem nonnegative7631 (p : Pattern) : 0 ≤ d7631 p :=
  nonnegative_ite (p 162) (nonnegative7630 p) (nonnegative7629 p)
def d7632 (p : Pattern) : Int := if p 161 then d7481 p else d7631 p
theorem agree7632 (p q : Pattern) (h : Agree support p q) : d7632 p = d7632 q := by
  simp only [d7632, h 161 (by decide), agree7481 p q h, agree7631 p q h]
theorem nonnegative7632 (p : Pattern) : 0 ≤ d7632 p :=
  nonnegative_ite (p 161) (nonnegative7481 p) (nonnegative7631 p)
def d7633 (p : Pattern) : Int := if p 160 then d7485 p else d7632 p
theorem agree7633 (p q : Pattern) (h : Agree support p q) : d7633 p = d7633 q := by
  simp only [d7633, h 160 (by decide), agree7485 p q h, agree7632 p q h]
theorem nonnegative7633 (p : Pattern) : 0 ≤ d7633 p :=
  nonnegative_ite (p 160) (nonnegative7485 p) (nonnegative7632 p)
def d7634 (p : Pattern) : Int := if p 225 then d11 p else d7 p
theorem agree7634 (p q : Pattern) (h : Agree support p q) : d7634 p = d7634 q := by
  simp only [d7634, h 225 (by decide), agree11 p q h, agree7 p q h]
theorem nonnegative7634 (p : Pattern) : 0 ≤ d7634 p :=
  nonnegative_ite (p 225) (nonnegative11 p) (nonnegative7 p)
def d7635 (p : Pattern) : Int := if p 224 then d7634 p else d7411 p
theorem agree7635 (p q : Pattern) (h : Agree support p q) : d7635 p = d7635 q := by
  simp only [d7635, h 224 (by decide), agree7634 p q h, agree7411 p q h]
theorem nonnegative7635 (p : Pattern) : 0 ≤ d7635 p :=
  nonnegative_ite (p 224) (nonnegative7634 p) (nonnegative7411 p)
def d7636 (p : Pattern) : Int := if p 204 then d12 p else d7635 p
theorem agree7636 (p q : Pattern) (h : Agree support p q) : d7636 p = d7636 q := by
  simp only [d7636, h 204 (by decide), agree12 p q h, agree7635 p q h]
theorem nonnegative7636 (p : Pattern) : 0 ≤ d7636 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7635 p)
def d7637 (p : Pattern) : Int := if p 182 then d7636 p else d7444 p
theorem agree7637 (p q : Pattern) (h : Agree support p q) : d7637 p = d7637 q := by
  simp only [d7637, h 182 (by decide), agree7636 p q h, agree7444 p q h]
theorem nonnegative7637 (p : Pattern) : 0 ≤ d7637 p :=
  nonnegative_ite (p 182) (nonnegative7636 p) (nonnegative7444 p)
def d7638 (p : Pattern) : Int := if p 163 then d7470 p else d7637 p
theorem agree7638 (p q : Pattern) (h : Agree support p q) : d7638 p = d7638 q := by
  simp only [d7638, h 163 (by decide), agree7470 p q h, agree7637 p q h]
theorem nonnegative7638 (p : Pattern) : 0 ≤ d7638 p :=
  nonnegative_ite (p 163) (nonnegative7470 p) (nonnegative7637 p)
def d7639 (p : Pattern) : Int := if p 162 then d7580 p else d7638 p
theorem agree7639 (p q : Pattern) (h : Agree support p q) : d7639 p = d7639 q := by
  simp only [d7639, h 162 (by decide), agree7580 p q h, agree7638 p q h]
theorem nonnegative7639 (p : Pattern) : 0 ≤ d7639 p :=
  nonnegative_ite (p 162) (nonnegative7580 p) (nonnegative7638 p)
def d7640 (p : Pattern) : Int := if p 161 then d7484 p else d7639 p
theorem agree7640 (p q : Pattern) (h : Agree support p q) : d7640 p = d7640 q := by
  simp only [d7640, h 161 (by decide), agree7484 p q h, agree7639 p q h]
theorem nonnegative7640 (p : Pattern) : 0 ≤ d7640 p :=
  nonnegative_ite (p 161) (nonnegative7484 p) (nonnegative7639 p)
def d7641 (p : Pattern) : Int := if p 162 then d12 p else d7353 p
theorem agree7641 (p q : Pattern) (h : Agree support p q) : d7641 p = d7641 q := by
  simp only [d7641, h 162 (by decide), agree12 p q h, agree7353 p q h]
theorem nonnegative7641 (p : Pattern) : 0 ≤ d7641 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7353 p)
def d7642 (p : Pattern) : Int := if p 161 then d12 p else d7641 p
theorem agree7642 (p q : Pattern) (h : Agree support p q) : d7642 p = d7642 q := by
  simp only [d7642, h 161 (by decide), agree12 p q h, agree7641 p q h]
theorem nonnegative7642 (p : Pattern) : 0 ≤ d7642 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7641 p)
def d7643 (p : Pattern) : Int := if p 160 then d7642 p else d7640 p
theorem agree7643 (p q : Pattern) (h : Agree support p q) : d7643 p = d7643 q := by
  simp only [d7643, h 160 (by decide), agree7642 p q h, agree7640 p q h]
theorem nonnegative7643 (p : Pattern) : 0 ≤ d7643 p :=
  nonnegative_ite (p 160) (nonnegative7642 p) (nonnegative7640 p)
def d7644 (p : Pattern) : Int := if p 141 then d7643 p else d7633 p
theorem agree7644 (p q : Pattern) (h : Agree support p q) : d7644 p = d7644 q := by
  simp only [d7644, h 141 (by decide), agree7643 p q h, agree7633 p q h]
theorem nonnegative7644 (p : Pattern) : 0 ≤ d7644 p :=
  nonnegative_ite (p 141) (nonnegative7643 p) (nonnegative7633 p)
def d7645 (p : Pattern) : Int := if p 138 then d7644 p else d7628 p
theorem agree7645 (p q : Pattern) (h : Agree support p q) : d7645 p = d7645 q := by
  simp only [d7645, h 138 (by decide), agree7644 p q h, agree7628 p q h]
theorem nonnegative7645 (p : Pattern) : 0 ≤ d7645 p :=
  nonnegative_ite (p 138) (nonnegative7644 p) (nonnegative7628 p)
def d7646 (p : Pattern) : Int := if p 163 then d7352 p else d7470 p
theorem agree7646 (p q : Pattern) (h : Agree support p q) : d7646 p = d7646 q := by
  simp only [d7646, h 163 (by decide), agree7352 p q h, agree7470 p q h]
theorem nonnegative7646 (p : Pattern) : 0 ≤ d7646 p :=
  nonnegative_ite (p 163) (nonnegative7352 p) (nonnegative7470 p)
def d7647 (p : Pattern) : Int := if p 162 then d7646 p else d7629 p
theorem agree7647 (p q : Pattern) (h : Agree support p q) : d7647 p = d7647 q := by
  simp only [d7647, h 162 (by decide), agree7646 p q h, agree7629 p q h]
theorem nonnegative7647 (p : Pattern) : 0 ≤ d7647 p :=
  nonnegative_ite (p 162) (nonnegative7646 p) (nonnegative7629 p)
def d7648 (p : Pattern) : Int := if p 163 then d7352 p else d7465 p
theorem agree7648 (p q : Pattern) (h : Agree support p q) : d7648 p = d7648 q := by
  simp only [d7648, h 163 (by decide), agree7352 p q h, agree7465 p q h]
theorem nonnegative7648 (p : Pattern) : 0 ≤ d7648 p :=
  nonnegative_ite (p 163) (nonnegative7352 p) (nonnegative7465 p)
def d7649 (p : Pattern) : Int := if p 162 then d12 p else d7648 p
theorem agree7649 (p q : Pattern) (h : Agree support p q) : d7649 p = d7649 q := by
  simp only [d7649, h 162 (by decide), agree12 p q h, agree7648 p q h]
theorem nonnegative7649 (p : Pattern) : 0 ≤ d7649 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7648 p)
def d7650 (p : Pattern) : Int := if p 161 then d7649 p else d7647 p
theorem agree7650 (p q : Pattern) (h : Agree support p q) : d7650 p = d7650 q := by
  simp only [d7650, h 161 (by decide), agree7649 p q h, agree7647 p q h]
theorem nonnegative7650 (p : Pattern) : 0 ≤ d7650 p :=
  nonnegative_ite (p 161) (nonnegative7649 p) (nonnegative7647 p)
def d7651 (p : Pattern) : Int := if p 163 then d7320 p else d7472 p
theorem agree7651 (p q : Pattern) (h : Agree support p q) : d7651 p = d7651 q := by
  simp only [d7651, h 163 (by decide), agree7320 p q h, agree7472 p q h]
theorem nonnegative7651 (p : Pattern) : 0 ≤ d7651 p :=
  nonnegative_ite (p 163) (nonnegative7320 p) (nonnegative7472 p)
def d7652 (p : Pattern) : Int := if p 162 then d12 p else d7651 p
theorem agree7652 (p q : Pattern) (h : Agree support p q) : d7652 p = d7652 q := by
  simp only [d7652, h 162 (by decide), agree12 p q h, agree7651 p q h]
theorem nonnegative7652 (p : Pattern) : 0 ≤ d7652 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7651 p)
def d7653 (p : Pattern) : Int := if p 161 then d12 p else d7652 p
theorem agree7653 (p q : Pattern) (h : Agree support p q) : d7653 p = d7653 q := by
  simp only [d7653, h 161 (by decide), agree12 p q h, agree7652 p q h]
theorem nonnegative7653 (p : Pattern) : 0 ≤ d7653 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7652 p)
def d7654 (p : Pattern) : Int := if p 160 then d7653 p else d7650 p
theorem agree7654 (p q : Pattern) (h : Agree support p q) : d7654 p = d7654 q := by
  simp only [d7654, h 160 (by decide), agree7653 p q h, agree7650 p q h]
theorem nonnegative7654 (p : Pattern) : 0 ≤ d7654 p :=
  nonnegative_ite (p 160) (nonnegative7653 p) (nonnegative7650 p)
def d7655 (p : Pattern) : Int := if p 141 then d7643 p else d7654 p
theorem agree7655 (p q : Pattern) (h : Agree support p q) : d7655 p = d7655 q := by
  simp only [d7655, h 141 (by decide), agree7643 p q h, agree7654 p q h]
theorem nonnegative7655 (p : Pattern) : 0 ≤ d7655 p :=
  nonnegative_ite (p 141) (nonnegative7643 p) (nonnegative7654 p)
def d7656 (p : Pattern) : Int := if p 138 then d12 p else d7655 p
theorem agree7656 (p q : Pattern) (h : Agree support p q) : d7656 p = d7656 q := by
  simp only [d7656, h 138 (by decide), agree12 p q h, agree7655 p q h]
theorem nonnegative7656 (p : Pattern) : 0 ≤ d7656 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7655 p)
def d7657 (p : Pattern) : Int := if p 116 then d7656 p else d7645 p
theorem agree7657 (p q : Pattern) (h : Agree support p q) : d7657 p = d7657 q := by
  simp only [d7657, h 116 (by decide), agree7656 p q h, agree7645 p q h]
theorem nonnegative7657 (p : Pattern) : 0 ≤ d7657 p :=
  nonnegative_ite (p 116) (nonnegative7656 p) (nonnegative7645 p)
def d7658 (p : Pattern) : Int := if p 115 then d7657 p else d7588 p
theorem agree7658 (p q : Pattern) (h : Agree support p q) : d7658 p = d7658 q := by
  simp only [d7658, h 115 (by decide), agree7657 p q h, agree7588 p q h]
theorem nonnegative7658 (p : Pattern) : 0 ≤ d7658 p :=
  nonnegative_ite (p 115) (nonnegative7657 p) (nonnegative7588 p)
def d7659 (p : Pattern) : Int := if p 71 then d7658 p else d7387 p
theorem agree7659 (p q : Pattern) (h : Agree support p q) : d7659 p = d7659 q := by
  simp only [d7659, h 71 (by decide), agree7658 p q h, agree7387 p q h]
theorem nonnegative7659 (p : Pattern) : 0 ≤ d7659 p :=
  nonnegative_ite (p 71) (nonnegative7658 p) (nonnegative7387 p)
def d7660 (p : Pattern) : Int := if p 49 then d7659 p else d7569 p
theorem agree7660 (p q : Pattern) (h : Agree support p q) : d7660 p = d7660 q := by
  simp only [d7660, h 49 (by decide), agree7659 p q h, agree7569 p q h]
theorem nonnegative7660 (p : Pattern) : 0 ≤ d7660 p :=
  nonnegative_ite (p 49) (nonnegative7659 p) (nonnegative7569 p)
def d7661 (p : Pattern) : Int := if p 48 then d7660 p else d7499 p
theorem agree7661 (p q : Pattern) (h : Agree support p q) : d7661 p = d7661 q := by
  simp only [d7661, h 48 (by decide), agree7660 p q h, agree7499 p q h]
theorem nonnegative7661 (p : Pattern) : 0 ≤ d7661 p :=
  nonnegative_ite (p 48) (nonnegative7660 p) (nonnegative7499 p)
def d7662 (p : Pattern) : Int := if p 225 then d3239 p else d3226 p
theorem agree7662 (p q : Pattern) (h : Agree support p q) : d7662 p = d7662 q := by
  simp only [d7662, h 225 (by decide), agree3239 p q h, agree3226 p q h]
theorem nonnegative7662 (p : Pattern) : 0 ≤ d7662 p :=
  nonnegative_ite (p 225) (nonnegative3239 p) (nonnegative3226 p)
def d7663 (p : Pattern) : Int := if p 224 then d3239 p else d7662 p
theorem agree7663 (p q : Pattern) (h : Agree support p q) : d7663 p = d7663 q := by
  simp only [d7663, h 224 (by decide), agree3239 p q h, agree7662 p q h]
theorem nonnegative7663 (p : Pattern) : 0 ≤ d7663 p :=
  nonnegative_ite (p 224) (nonnegative3239 p) (nonnegative7662 p)
def d7664 (p : Pattern) : Int := if p 204 then d7663 p else d3226 p
theorem agree7664 (p q : Pattern) (h : Agree support p q) : d7664 p = d7664 q := by
  simp only [d7664, h 204 (by decide), agree7663 p q h, agree3226 p q h]
theorem nonnegative7664 (p : Pattern) : 0 ≤ d7664 p :=
  nonnegative_ite (p 204) (nonnegative7663 p) (nonnegative3226 p)
def d7665 (p : Pattern) : Int := if p 225 then d3250 p else d3226 p
theorem agree7665 (p q : Pattern) (h : Agree support p q) : d7665 p = d7665 q := by
  simp only [d7665, h 225 (by decide), agree3250 p q h, agree3226 p q h]
theorem nonnegative7665 (p : Pattern) : 0 ≤ d7665 p :=
  nonnegative_ite (p 225) (nonnegative3250 p) (nonnegative3226 p)
def d7666 (p : Pattern) : Int := if p 224 then d3250 p else d7665 p
theorem agree7666 (p q : Pattern) (h : Agree support p q) : d7666 p = d7666 q := by
  simp only [d7666, h 224 (by decide), agree3250 p q h, agree7665 p q h]
theorem nonnegative7666 (p : Pattern) : 0 ≤ d7666 p :=
  nonnegative_ite (p 224) (nonnegative3250 p) (nonnegative7665 p)
def d7667 (p : Pattern) : Int := if p 204 then d12 p else d7666 p
theorem agree7667 (p q : Pattern) (h : Agree support p q) : d7667 p = d7667 q := by
  simp only [d7667, h 204 (by decide), agree12 p q h, agree7666 p q h]
theorem nonnegative7667 (p : Pattern) : 0 ≤ d7667 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7666 p)
def d7668 (p : Pattern) : Int := if p 182 then d7667 p else d7664 p
theorem agree7668 (p q : Pattern) (h : Agree support p q) : d7668 p = d7668 q := by
  simp only [d7668, h 182 (by decide), agree7667 p q h, agree7664 p q h]
theorem nonnegative7668 (p : Pattern) : 0 ≤ d7668 p :=
  nonnegative_ite (p 182) (nonnegative7667 p) (nonnegative7664 p)
def d7669 (p : Pattern) : Int := if p 225 then d3461 p else d3239 p
theorem agree7669 (p q : Pattern) (h : Agree support p q) : d7669 p = d7669 q := by
  simp only [d7669, h 225 (by decide), agree3461 p q h, agree3239 p q h]
theorem nonnegative7669 (p : Pattern) : 0 ≤ d7669 p :=
  nonnegative_ite (p 225) (nonnegative3461 p) (nonnegative3239 p)
def d7670 (p : Pattern) : Int := if p 224 then d3461 p else d7669 p
theorem agree7670 (p q : Pattern) (h : Agree support p q) : d7670 p = d7670 q := by
  simp only [d7670, h 224 (by decide), agree3461 p q h, agree7669 p q h]
theorem nonnegative7670 (p : Pattern) : 0 ≤ d7670 p :=
  nonnegative_ite (p 224) (nonnegative3461 p) (nonnegative7669 p)
def d7671 (p : Pattern) : Int := if p 204 then d7670 p else d3239 p
theorem agree7671 (p q : Pattern) (h : Agree support p q) : d7671 p = d7671 q := by
  simp only [d7671, h 204 (by decide), agree7670 p q h, agree3239 p q h]
theorem nonnegative7671 (p : Pattern) : 0 ≤ d7671 p :=
  nonnegative_ite (p 204) (nonnegative7670 p) (nonnegative3239 p)
def d7672 (p : Pattern) : Int := if p 225 then d3253 p else d3239 p
theorem agree7672 (p q : Pattern) (h : Agree support p q) : d7672 p = d7672 q := by
  simp only [d7672, h 225 (by decide), agree3253 p q h, agree3239 p q h]
theorem nonnegative7672 (p : Pattern) : 0 ≤ d7672 p :=
  nonnegative_ite (p 225) (nonnegative3253 p) (nonnegative3239 p)
def d7673 (p : Pattern) : Int := if p 224 then d3253 p else d7672 p
theorem agree7673 (p q : Pattern) (h : Agree support p q) : d7673 p = d7673 q := by
  simp only [d7673, h 224 (by decide), agree3253 p q h, agree7672 p q h]
theorem nonnegative7673 (p : Pattern) : 0 ≤ d7673 p :=
  nonnegative_ite (p 224) (nonnegative3253 p) (nonnegative7672 p)
def d7674 (p : Pattern) : Int := if p 204 then d12 p else d7673 p
theorem agree7674 (p q : Pattern) (h : Agree support p q) : d7674 p = d7674 q := by
  simp only [d7674, h 204 (by decide), agree12 p q h, agree7673 p q h]
theorem nonnegative7674 (p : Pattern) : 0 ≤ d7674 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7673 p)
def d7675 (p : Pattern) : Int := if p 182 then d7674 p else d7671 p
theorem agree7675 (p q : Pattern) (h : Agree support p q) : d7675 p = d7675 q := by
  simp only [d7675, h 182 (by decide), agree7674 p q h, agree7671 p q h]
theorem nonnegative7675 (p : Pattern) : 0 ≤ d7675 p :=
  nonnegative_ite (p 182) (nonnegative7674 p) (nonnegative7671 p)
def d7676 (p : Pattern) : Int := if p 163 then d7675 p else d7668 p
theorem agree7676 (p q : Pattern) (h : Agree support p q) : d7676 p = d7676 q := by
  simp only [d7676, h 163 (by decide), agree7675 p q h, agree7668 p q h]
theorem nonnegative7676 (p : Pattern) : 0 ≤ d7676 p :=
  nonnegative_ite (p 163) (nonnegative7675 p) (nonnegative7668 p)
def d7677 (p : Pattern) : Int := if p 162 then d7676 p else d7668 p
theorem agree7677 (p q : Pattern) (h : Agree support p q) : d7677 p = d7677 q := by
  simp only [d7677, h 162 (by decide), agree7676 p q h, agree7668 p q h]
theorem nonnegative7677 (p : Pattern) : 0 ≤ d7677 p :=
  nonnegative_ite (p 162) (nonnegative7676 p) (nonnegative7668 p)
def d7678 (p : Pattern) : Int := if p 225 then d12 p else d3244 p
theorem agree7678 (p q : Pattern) (h : Agree support p q) : d7678 p = d7678 q := by
  simp only [d7678, h 225 (by decide), agree12 p q h, agree3244 p q h]
theorem nonnegative7678 (p : Pattern) : 0 ≤ d7678 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative3244 p)
def d7679 (p : Pattern) : Int := if p 224 then d12 p else d7678 p
theorem agree7679 (p q : Pattern) (h : Agree support p q) : d7679 p = d7679 q := by
  simp only [d7679, h 224 (by decide), agree12 p q h, agree7678 p q h]
theorem nonnegative7679 (p : Pattern) : 0 ≤ d7679 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative7678 p)
end NetHack.Sokoban22Refined85
