/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d600 (p : Pattern) : Int := if p 138 then d564 p else d545 p
theorem agree600 (p q : Pattern) (h : Agree support p q) : d600 p = d600 q := by
  simp only [d600, h 138 (by decide), agree564 p q h, agree545 p q h]
theorem nonnegative600 (p : Pattern) : 0 ≤ d600 p :=
  nonnegative_ite (p 138) (nonnegative564 p) (nonnegative545 p)
def d601 (p : Pattern) : Int := if p 134 then d600 p else d598 p
theorem agree601 (p q : Pattern) (h : Agree support p q) : d601 p = d601 q := by
  simp only [d601, h 134 (by decide), agree600 p q h, agree598 p q h]
theorem nonnegative601 (p : Pattern) : 0 ≤ d601 p :=
  nonnegative_ite (p 134) (nonnegative600 p) (nonnegative598 p)
def d602 (p : Pattern) : Int := if p 133 then d601 p else d599 p
theorem agree602 (p q : Pattern) (h : Agree support p q) : d602 p = d602 q := by
  simp only [d602, h 133 (by decide), agree601 p q h, agree599 p q h]
theorem nonnegative602 (p : Pattern) : 0 ≤ d602 p :=
  nonnegative_ite (p 133) (nonnegative601 p) (nonnegative599 p)
def d603 (p : Pattern) : Int := if p 138 then d562 p else d583 p
theorem agree603 (p q : Pattern) (h : Agree support p q) : d603 p = d603 q := by
  simp only [d603, h 138 (by decide), agree562 p q h, agree583 p q h]
theorem nonnegative603 (p : Pattern) : 0 ≤ d603 p :=
  nonnegative_ite (p 138) (nonnegative562 p) (nonnegative583 p)
def d604 (p : Pattern) : Int := if p 138 then d568 p else d551 p
theorem agree604 (p q : Pattern) (h : Agree support p q) : d604 p = d604 q := by
  simp only [d604, h 138 (by decide), agree568 p q h, agree551 p q h]
theorem nonnegative604 (p : Pattern) : 0 ≤ d604 p :=
  nonnegative_ite (p 138) (nonnegative568 p) (nonnegative551 p)
def d605 (p : Pattern) : Int := if p 134 then d604 p else d603 p
theorem agree605 (p q : Pattern) (h : Agree support p q) : d605 p = d605 q := by
  simp only [d605, h 134 (by decide), agree604 p q h, agree603 p q h]
theorem nonnegative605 (p : Pattern) : 0 ≤ d605 p :=
  nonnegative_ite (p 134) (nonnegative604 p) (nonnegative603 p)
def d606 (p : Pattern) : Int := if p 133 then d601 p else d605 p
theorem agree606 (p q : Pattern) (h : Agree support p q) : d606 p = d606 q := by
  simp only [d606, h 133 (by decide), agree601 p q h, agree605 p q h]
theorem nonnegative606 (p : Pattern) : 0 ≤ d606 p :=
  nonnegative_ite (p 133) (nonnegative601 p) (nonnegative605 p)
def d607 (p : Pattern) : Int := if p 132 then d606 p else d602 p
theorem agree607 (p q : Pattern) (h : Agree support p q) : d607 p = d607 q := by
  simp only [d607, h 132 (by decide), agree606 p q h, agree602 p q h]
theorem nonnegative607 (p : Pattern) : 0 ≤ d607 p :=
  nonnegative_ite (p 132) (nonnegative606 p) (nonnegative602 p)
def d608 (p : Pattern) : Int := if p 113 then d607 p else d556 p
theorem agree608 (p q : Pattern) (h : Agree support p q) : d608 p = d608 q := by
  simp only [d608, h 113 (by decide), agree607 p q h, agree556 p q h]
theorem nonnegative608 (p : Pattern) : 0 ≤ d608 p :=
  nonnegative_ite (p 113) (nonnegative607 p) (nonnegative556 p)
def d609 (p : Pattern) : Int := if p 133 then d580 p else d577 p
theorem agree609 (p q : Pattern) (h : Agree support p q) : d609 p = d609 q := by
  simp only [d609, h 133 (by decide), agree580 p q h, agree577 p q h]
theorem nonnegative609 (p : Pattern) : 0 ≤ d609 p :=
  nonnegative_ite (p 133) (nonnegative580 p) (nonnegative577 p)
def d610 (p : Pattern) : Int := if p 132 then d580 p else d609 p
theorem agree610 (p q : Pattern) (h : Agree support p q) : d610 p = d610 q := by
  simp only [d610, h 132 (by decide), agree580 p q h, agree609 p q h]
theorem nonnegative610 (p : Pattern) : 0 ≤ d610 p :=
  nonnegative_ite (p 132) (nonnegative580 p) (nonnegative609 p)
def d611 (p : Pattern) : Int := if p 112 then d610 p else d608 p
theorem agree611 (p q : Pattern) (h : Agree support p q) : d611 p = d611 q := by
  simp only [d611, h 112 (by decide), agree610 p q h, agree608 p q h]
theorem nonnegative611 (p : Pattern) : 0 ≤ d611 p :=
  nonnegative_ite (p 112) (nonnegative610 p) (nonnegative608 p)
def d612 (p : Pattern) : Int := if p 134 then d598 p else d603 p
theorem agree612 (p q : Pattern) (h : Agree support p q) : d612 p = d612 q := by
  simp only [d612, h 134 (by decide), agree598 p q h, agree603 p q h]
theorem nonnegative612 (p : Pattern) : 0 ≤ d612 p :=
  nonnegative_ite (p 134) (nonnegative598 p) (nonnegative603 p)
def d613 (p : Pattern) : Int := if p 133 then d601 p else d612 p
theorem agree613 (p q : Pattern) (h : Agree support p q) : d613 p = d613 q := by
  simp only [d613, h 133 (by decide), agree601 p q h, agree612 p q h]
theorem nonnegative613 (p : Pattern) : 0 ≤ d613 p :=
  nonnegative_ite (p 133) (nonnegative601 p) (nonnegative612 p)
def d614 (p : Pattern) : Int := if p 133 then d586 p else d601 p
theorem agree614 (p q : Pattern) (h : Agree support p q) : d614 p = d614 q := by
  simp only [d614, h 133 (by decide), agree586 p q h, agree601 p q h]
theorem nonnegative614 (p : Pattern) : 0 ≤ d614 p :=
  nonnegative_ite (p 133) (nonnegative586 p) (nonnegative601 p)
def d615 (p : Pattern) : Int := if p 132 then d614 p else d613 p
theorem agree615 (p q : Pattern) (h : Agree support p q) : d615 p = d615 q := by
  simp only [d615, h 132 (by decide), agree614 p q h, agree613 p q h]
theorem nonnegative615 (p : Pattern) : 0 ≤ d615 p :=
  nonnegative_ite (p 132) (nonnegative614 p) (nonnegative613 p)
def d616 (p : Pattern) : Int := if p 113 then d615 p else d588 p
theorem agree616 (p q : Pattern) (h : Agree support p q) : d616 p = d616 q := by
  simp only [d616, h 113 (by decide), agree615 p q h, agree588 p q h]
theorem nonnegative616 (p : Pattern) : 0 ≤ d616 p :=
  nonnegative_ite (p 113) (nonnegative615 p) (nonnegative588 p)
def d617 (p : Pattern) : Int := if p 133 then d2 p else d580 p
theorem agree617 (p q : Pattern) (h : Agree support p q) : d617 p = d617 q := by
  simp only [d617, h 133 (by decide), agree2 p q h, agree580 p q h]
theorem nonnegative617 (p : Pattern) : 0 ≤ d617 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative580 p)
def d618 (p : Pattern) : Int := if p 132 then d617 p else d609 p
theorem agree618 (p q : Pattern) (h : Agree support p q) : d618 p = d618 q := by
  simp only [d618, h 132 (by decide), agree617 p q h, agree609 p q h]
theorem nonnegative618 (p : Pattern) : 0 ≤ d618 p :=
  nonnegative_ite (p 132) (nonnegative617 p) (nonnegative609 p)
def d619 (p : Pattern) : Int := if p 133 then d586 p else d576 p
theorem agree619 (p q : Pattern) (h : Agree support p q) : d619 p = d619 q := by
  simp only [d619, h 133 (by decide), agree586 p q h, agree576 p q h]
theorem nonnegative619 (p : Pattern) : 0 ≤ d619 p :=
  nonnegative_ite (p 133) (nonnegative586 p) (nonnegative576 p)
def d620 (p : Pattern) : Int := if p 133 then d2 p else d586 p
theorem agree620 (p q : Pattern) (h : Agree support p q) : d620 p = d620 q := by
  simp only [d620, h 133 (by decide), agree2 p q h, agree586 p q h]
theorem nonnegative620 (p : Pattern) : 0 ≤ d620 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative586 p)
def d621 (p : Pattern) : Int := if p 132 then d620 p else d619 p
theorem agree621 (p q : Pattern) (h : Agree support p q) : d621 p = d621 q := by
  simp only [d621, h 132 (by decide), agree620 p q h, agree619 p q h]
theorem nonnegative621 (p : Pattern) : 0 ≤ d621 p :=
  nonnegative_ite (p 132) (nonnegative620 p) (nonnegative619 p)
def d622 (p : Pattern) : Int := if p 113 then d621 p else d618 p
theorem agree622 (p q : Pattern) (h : Agree support p q) : d622 p = d622 q := by
  simp only [d622, h 113 (by decide), agree621 p q h, agree618 p q h]
theorem nonnegative622 (p : Pattern) : 0 ≤ d622 p :=
  nonnegative_ite (p 113) (nonnegative621 p) (nonnegative618 p)
def d623 (p : Pattern) : Int := if p 112 then d622 p else d616 p
theorem agree623 (p q : Pattern) (h : Agree support p q) : d623 p = d623 q := by
  simp only [d623, h 112 (by decide), agree622 p q h, agree616 p q h]
theorem nonnegative623 (p : Pattern) : 0 ≤ d623 p :=
  nonnegative_ite (p 112) (nonnegative622 p) (nonnegative616 p)
def d624 (p : Pattern) : Int := if p 106 then d623 p else d611 p
theorem agree624 (p q : Pattern) (h : Agree support p q) : d624 p = d624 q := by
  simp only [d624, h 106 (by decide), agree623 p q h, agree611 p q h]
theorem nonnegative624 (p : Pattern) : 0 ≤ d624 p :=
  nonnegative_ite (p 106) (nonnegative623 p) (nonnegative611 p)
def d625 (p : Pattern) : Int := if p 86 then d624 p else d596 p
theorem agree625 (p q : Pattern) (h : Agree support p q) : d625 p = d625 q := by
  simp only [d625, h 86 (by decide), agree624 p q h, agree596 p q h]
theorem nonnegative625 (p : Pattern) : 0 ≤ d625 p :=
  nonnegative_ite (p 86) (nonnegative624 p) (nonnegative596 p)
def d626 (p : Pattern) : Int := if p 134 then d553 p else d584 p
theorem agree626 (p q : Pattern) (h : Agree support p q) : d626 p = d626 q := by
  simp only [d626, h 134 (by decide), agree553 p q h, agree584 p q h]
theorem nonnegative626 (p : Pattern) : 0 ≤ d626 p :=
  nonnegative_ite (p 134) (nonnegative553 p) (nonnegative584 p)
def d627 (p : Pattern) : Int := if p 133 then d549 p else d626 p
theorem agree627 (p q : Pattern) (h : Agree support p q) : d627 p = d627 q := by
  simp only [d627, h 133 (by decide), agree549 p q h, agree626 p q h]
theorem nonnegative627 (p : Pattern) : 0 ≤ d627 p :=
  nonnegative_ite (p 133) (nonnegative549 p) (nonnegative626 p)
def d628 (p : Pattern) : Int := if p 132 then d627 p else d550 p
theorem agree628 (p q : Pattern) (h : Agree support p q) : d628 p = d628 q := by
  simp only [d628, h 132 (by decide), agree627 p q h, agree550 p q h]
theorem nonnegative628 (p : Pattern) : 0 ≤ d628 p :=
  nonnegative_ite (p 132) (nonnegative627 p) (nonnegative550 p)
def d629 (p : Pattern) : Int := if p 113 then d628 p else d556 p
theorem agree629 (p q : Pattern) (h : Agree support p q) : d629 p = d629 q := by
  simp only [d629, h 113 (by decide), agree628 p q h, agree556 p q h]
theorem nonnegative629 (p : Pattern) : 0 ≤ d629 p :=
  nonnegative_ite (p 113) (nonnegative628 p) (nonnegative556 p)
def d630 (p : Pattern) : Int := if p 112 then d573 p else d629 p
theorem agree630 (p q : Pattern) (h : Agree support p q) : d630 p = d630 q := by
  simp only [d630, h 112 (by decide), agree573 p q h, agree629 p q h]
theorem nonnegative630 (p : Pattern) : 0 ≤ d630 p :=
  nonnegative_ite (p 112) (nonnegative573 p) (nonnegative629 p)
def d631 (p : Pattern) : Int := if p 134 then d543 p else d584 p
theorem agree631 (p q : Pattern) (h : Agree support p q) : d631 p = d631 q := by
  simp only [d631, h 134 (by decide), agree543 p q h, agree584 p q h]
theorem nonnegative631 (p : Pattern) : 0 ≤ d631 p :=
  nonnegative_ite (p 134) (nonnegative543 p) (nonnegative584 p)
def d632 (p : Pattern) : Int := if p 133 then d549 p else d631 p
theorem agree632 (p q : Pattern) (h : Agree support p q) : d632 p = d632 q := by
  simp only [d632, h 133 (by decide), agree549 p q h, agree631 p q h]
theorem nonnegative632 (p : Pattern) : 0 ≤ d632 p :=
  nonnegative_ite (p 133) (nonnegative549 p) (nonnegative631 p)
def d633 (p : Pattern) : Int := if p 133 then d586 p else d549 p
theorem agree633 (p q : Pattern) (h : Agree support p q) : d633 p = d633 q := by
  simp only [d633, h 133 (by decide), agree586 p q h, agree549 p q h]
theorem nonnegative633 (p : Pattern) : 0 ≤ d633 p :=
  nonnegative_ite (p 133) (nonnegative586 p) (nonnegative549 p)
def d634 (p : Pattern) : Int := if p 132 then d633 p else d632 p
theorem agree634 (p q : Pattern) (h : Agree support p q) : d634 p = d634 q := by
  simp only [d634, h 132 (by decide), agree633 p q h, agree632 p q h]
theorem nonnegative634 (p : Pattern) : 0 ≤ d634 p :=
  nonnegative_ite (p 132) (nonnegative633 p) (nonnegative632 p)
def d635 (p : Pattern) : Int := if p 113 then d634 p else d588 p
theorem agree635 (p q : Pattern) (h : Agree support p q) : d635 p = d635 q := by
  simp only [d635, h 113 (by decide), agree634 p q h, agree588 p q h]
theorem nonnegative635 (p : Pattern) : 0 ≤ d635 p :=
  nonnegative_ite (p 113) (nonnegative634 p) (nonnegative588 p)
def d636 (p : Pattern) : Int := if p 112 then d594 p else d635 p
theorem agree636 (p q : Pattern) (h : Agree support p q) : d636 p = d636 q := by
  simp only [d636, h 112 (by decide), agree594 p q h, agree635 p q h]
theorem nonnegative636 (p : Pattern) : 0 ≤ d636 p :=
  nonnegative_ite (p 112) (nonnegative594 p) (nonnegative635 p)
def d637 (p : Pattern) : Int := if p 106 then d636 p else d630 p
theorem agree637 (p q : Pattern) (h : Agree support p q) : d637 p = d637 q := by
  simp only [d637, h 106 (by decide), agree636 p q h, agree630 p q h]
theorem nonnegative637 (p : Pattern) : 0 ≤ d637 p :=
  nonnegative_ite (p 106) (nonnegative636 p) (nonnegative630 p)
def d638 (p : Pattern) : Int := if p 139 then d545 p else d551 p
theorem agree638 (p q : Pattern) (h : Agree support p q) : d638 p = d638 q := by
  simp only [d638, h 139 (by decide), agree545 p q h, agree551 p q h]
theorem nonnegative638 (p : Pattern) : 0 ≤ d638 p :=
  nonnegative_ite (p 139) (nonnegative545 p) (nonnegative551 p)
def d639 (p : Pattern) : Int := if p 138 then d568 p else d638 p
theorem agree639 (p q : Pattern) (h : Agree support p q) : d639 p = d639 q := by
  simp only [d639, h 138 (by decide), agree568 p q h, agree638 p q h]
theorem nonnegative639 (p : Pattern) : 0 ≤ d639 p :=
  nonnegative_ite (p 138) (nonnegative568 p) (nonnegative638 p)
def d640 (p : Pattern) : Int := if p 134 then d639 p else d598 p
theorem agree640 (p q : Pattern) (h : Agree support p q) : d640 p = d640 q := by
  simp only [d640, h 134 (by decide), agree639 p q h, agree598 p q h]
theorem nonnegative640 (p : Pattern) : 0 ≤ d640 p :=
  nonnegative_ite (p 134) (nonnegative639 p) (nonnegative598 p)
def d641 (p : Pattern) : Int := if p 133 then d601 p else d640 p
theorem agree641 (p q : Pattern) (h : Agree support p q) : d641 p = d641 q := by
  simp only [d641, h 133 (by decide), agree601 p q h, agree640 p q h]
theorem nonnegative641 (p : Pattern) : 0 ≤ d641 p :=
  nonnegative_ite (p 133) (nonnegative601 p) (nonnegative640 p)
def d642 (p : Pattern) : Int := if p 132 then d641 p else d613 p
theorem agree642 (p q : Pattern) (h : Agree support p q) : d642 p = d642 q := by
  simp only [d642, h 132 (by decide), agree641 p q h, agree613 p q h]
theorem nonnegative642 (p : Pattern) : 0 ≤ d642 p :=
  nonnegative_ite (p 132) (nonnegative641 p) (nonnegative613 p)
def d643 (p : Pattern) : Int := if p 113 then d642 p else d628 p
theorem agree643 (p q : Pattern) (h : Agree support p q) : d643 p = d643 q := by
  simp only [d643, h 113 (by decide), agree642 p q h, agree628 p q h]
theorem nonnegative643 (p : Pattern) : 0 ≤ d643 p :=
  nonnegative_ite (p 113) (nonnegative642 p) (nonnegative628 p)
def d644 (p : Pattern) : Int := if p 132 then d586 p else d619 p
theorem agree644 (p q : Pattern) (h : Agree support p q) : d644 p = d644 q := by
  simp only [d644, h 132 (by decide), agree586 p q h, agree619 p q h]
theorem nonnegative644 (p : Pattern) : 0 ≤ d644 p :=
  nonnegative_ite (p 132) (nonnegative586 p) (nonnegative619 p)
def d645 (p : Pattern) : Int := if p 113 then d644 p else d610 p
theorem agree645 (p q : Pattern) (h : Agree support p q) : d645 p = d645 q := by
  simp only [d645, h 113 (by decide), agree644 p q h, agree610 p q h]
theorem nonnegative645 (p : Pattern) : 0 ≤ d645 p :=
  nonnegative_ite (p 113) (nonnegative644 p) (nonnegative610 p)
def d646 (p : Pattern) : Int := if p 112 then d645 p else d643 p
theorem agree646 (p q : Pattern) (h : Agree support p q) : d646 p = d646 q := by
  simp only [d646, h 112 (by decide), agree645 p q h, agree643 p q h]
theorem nonnegative646 (p : Pattern) : 0 ≤ d646 p :=
  nonnegative_ite (p 112) (nonnegative645 p) (nonnegative643 p)
def d647 (p : Pattern) : Int := if p 113 then d593 p else d634 p
theorem agree647 (p q : Pattern) (h : Agree support p q) : d647 p = d647 q := by
  simp only [d647, h 113 (by decide), agree593 p q h, agree634 p q h]
theorem nonnegative647 (p : Pattern) : 0 ≤ d647 p :=
  nonnegative_ite (p 113) (nonnegative593 p) (nonnegative634 p)
def d648 (p : Pattern) : Int := if p 113 then d2 p else d621 p
theorem agree648 (p q : Pattern) (h : Agree support p q) : d648 p = d648 q := by
  simp only [d648, h 113 (by decide), agree2 p q h, agree621 p q h]
theorem nonnegative648 (p : Pattern) : 0 ≤ d648 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative621 p)
def d649 (p : Pattern) : Int := if p 112 then d648 p else d647 p
theorem agree649 (p q : Pattern) (h : Agree support p q) : d649 p = d649 q := by
  simp only [d649, h 112 (by decide), agree648 p q h, agree647 p q h]
theorem nonnegative649 (p : Pattern) : 0 ≤ d649 p :=
  nonnegative_ite (p 112) (nonnegative648 p) (nonnegative647 p)
def d650 (p : Pattern) : Int := if p 106 then d649 p else d646 p
theorem agree650 (p q : Pattern) (h : Agree support p q) : d650 p = d650 q := by
  simp only [d650, h 106 (by decide), agree649 p q h, agree646 p q h]
theorem nonnegative650 (p : Pattern) : 0 ≤ d650 p :=
  nonnegative_ite (p 106) (nonnegative649 p) (nonnegative646 p)
def d651 (p : Pattern) : Int := if p 86 then d650 p else d637 p
theorem agree651 (p q : Pattern) (h : Agree support p q) : d651 p = d651 q := by
  simp only [d651, h 86 (by decide), agree650 p q h, agree637 p q h]
theorem nonnegative651 (p : Pattern) : 0 ≤ d651 p :=
  nonnegative_ite (p 86) (nonnegative650 p) (nonnegative637 p)
def d652 (p : Pattern) : Int := if p 80 then d651 p else d625 p
theorem agree652 (p q : Pattern) (h : Agree support p q) : d652 p = d652 q := by
  simp only [d652, h 80 (by decide), agree651 p q h, agree625 p q h]
theorem nonnegative652 (p : Pattern) : 0 ≤ d652 p :=
  nonnegative_ite (p 80) (nonnegative651 p) (nonnegative625 p)
def d653 (p : Pattern) : Int := if p 139 then d13 p else d7 p
theorem agree653 (p q : Pattern) (h : Agree support p q) : d653 p = d653 q := by
  simp only [d653, h 139 (by decide), agree13 p q h, agree7 p q h]
theorem nonnegative653 (p : Pattern) : 0 ≤ d653 p :=
  nonnegative_ite (p 139) (nonnegative13 p) (nonnegative7 p)
def d654 (p : Pattern) : Int := if p 138 then d653 p else d7 p
theorem agree654 (p q : Pattern) (h : Agree support p q) : d654 p = d654 q := by
  simp only [d654, h 138 (by decide), agree653 p q h, agree7 p q h]
theorem nonnegative654 (p : Pattern) : 0 ≤ d654 p :=
  nonnegative_ite (p 138) (nonnegative653 p) (nonnegative7 p)
def d655 (p : Pattern) : Int := if p 139 then d2 p else d7 p
theorem agree655 (p q : Pattern) (h : Agree support p q) : d655 p = d655 q := by
  simp only [d655, h 139 (by decide), agree2 p q h, agree7 p q h]
theorem nonnegative655 (p : Pattern) : 0 ≤ d655 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative7 p)
def d656 (p : Pattern) : Int := if p 138 then d655 p else d653 p
theorem agree656 (p q : Pattern) (h : Agree support p q) : d656 p = d656 q := by
  simp only [d656, h 138 (by decide), agree655 p q h, agree653 p q h]
theorem nonnegative656 (p : Pattern) : 0 ≤ d656 p :=
  nonnegative_ite (p 138) (nonnegative655 p) (nonnegative653 p)
def d657 (p : Pattern) : Int := if p 113 then d656 p else d653 p
theorem agree657 (p q : Pattern) (h : Agree support p q) : d657 p = d657 q := by
  simp only [d657, h 113 (by decide), agree656 p q h, agree653 p q h]
theorem nonnegative657 (p : Pattern) : 0 ≤ d657 p :=
  nonnegative_ite (p 113) (nonnegative656 p) (nonnegative653 p)
def d658 (p : Pattern) : Int := if p 112 then d657 p else d654 p
theorem agree658 (p q : Pattern) (h : Agree support p q) : d658 p = d658 q := by
  simp only [d658, h 112 (by decide), agree657 p q h, agree654 p q h]
theorem nonnegative658 (p : Pattern) : 0 ≤ d658 p :=
  nonnegative_ite (p 112) (nonnegative657 p) (nonnegative654 p)
def d659 (p : Pattern) : Int := if p 139 then d2 p else d13 p
theorem agree659 (p q : Pattern) (h : Agree support p q) : d659 p = d659 q := by
  simp only [d659, h 139 (by decide), agree2 p q h, agree13 p q h]
theorem nonnegative659 (p : Pattern) : 0 ≤ d659 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative13 p)
def d660 (p : Pattern) : Int := if p 138 then d659 p else d13 p
theorem agree660 (p q : Pattern) (h : Agree support p q) : d660 p = d660 q := by
  simp only [d660, h 138 (by decide), agree659 p q h, agree13 p q h]
theorem nonnegative660 (p : Pattern) : 0 ≤ d660 p :=
  nonnegative_ite (p 138) (nonnegative659 p) (nonnegative13 p)
def d661 (p : Pattern) : Int := if p 133 then d660 p else d654 p
theorem agree661 (p q : Pattern) (h : Agree support p q) : d661 p = d661 q := by
  simp only [d661, h 133 (by decide), agree660 p q h, agree654 p q h]
theorem nonnegative661 (p : Pattern) : 0 ≤ d661 p :=
  nonnegative_ite (p 133) (nonnegative660 p) (nonnegative654 p)
def d662 (p : Pattern) : Int := if p 132 then d661 p else d654 p
theorem agree662 (p q : Pattern) (h : Agree support p q) : d662 p = d662 q := by
  simp only [d662, h 132 (by decide), agree661 p q h, agree654 p q h]
theorem nonnegative662 (p : Pattern) : 0 ≤ d662 p :=
  nonnegative_ite (p 132) (nonnegative661 p) (nonnegative654 p)
def d663 (p : Pattern) : Int := if p 133 then d659 p else d654 p
theorem agree663 (p q : Pattern) (h : Agree support p q) : d663 p = d663 q := by
  simp only [d663, h 133 (by decide), agree659 p q h, agree654 p q h]
theorem nonnegative663 (p : Pattern) : 0 ≤ d663 p :=
  nonnegative_ite (p 133) (nonnegative659 p) (nonnegative654 p)
def d664 (p : Pattern) : Int := if p 132 then d663 p else d654 p
theorem agree664 (p q : Pattern) (h : Agree support p q) : d664 p = d664 q := by
  simp only [d664, h 132 (by decide), agree663 p q h, agree654 p q h]
theorem nonnegative664 (p : Pattern) : 0 ≤ d664 p :=
  nonnegative_ite (p 132) (nonnegative663 p) (nonnegative654 p)
def d665 (p : Pattern) : Int := if p 113 then d664 p else d662 p
theorem agree665 (p q : Pattern) (h : Agree support p q) : d665 p = d665 q := by
  simp only [d665, h 113 (by decide), agree664 p q h, agree662 p q h]
theorem nonnegative665 (p : Pattern) : 0 ≤ d665 p :=
  nonnegative_ite (p 113) (nonnegative664 p) (nonnegative662 p)
def d666 (p : Pattern) : Int := if p 133 then d659 p else d653 p
theorem agree666 (p q : Pattern) (h : Agree support p q) : d666 p = d666 q := by
  simp only [d666, h 133 (by decide), agree659 p q h, agree653 p q h]
theorem nonnegative666 (p : Pattern) : 0 ≤ d666 p :=
  nonnegative_ite (p 133) (nonnegative659 p) (nonnegative653 p)
def d667 (p : Pattern) : Int := if p 132 then d666 p else d653 p
theorem agree667 (p q : Pattern) (h : Agree support p q) : d667 p = d667 q := by
  simp only [d667, h 132 (by decide), agree666 p q h, agree653 p q h]
theorem nonnegative667 (p : Pattern) : 0 ≤ d667 p :=
  nonnegative_ite (p 132) (nonnegative666 p) (nonnegative653 p)
def d668 (p : Pattern) : Int := if p 133 then d659 p else d656 p
theorem agree668 (p q : Pattern) (h : Agree support p q) : d668 p = d668 q := by
  simp only [d668, h 133 (by decide), agree659 p q h, agree656 p q h]
theorem nonnegative668 (p : Pattern) : 0 ≤ d668 p :=
  nonnegative_ite (p 133) (nonnegative659 p) (nonnegative656 p)
def d669 (p : Pattern) : Int := if p 132 then d668 p else d656 p
theorem agree669 (p q : Pattern) (h : Agree support p q) : d669 p = d669 q := by
  simp only [d669, h 132 (by decide), agree668 p q h, agree656 p q h]
theorem nonnegative669 (p : Pattern) : 0 ≤ d669 p :=
  nonnegative_ite (p 132) (nonnegative668 p) (nonnegative656 p)
def d670 (p : Pattern) : Int := if p 113 then d669 p else d667 p
theorem agree670 (p q : Pattern) (h : Agree support p q) : d670 p = d670 q := by
  simp only [d670, h 113 (by decide), agree669 p q h, agree667 p q h]
theorem nonnegative670 (p : Pattern) : 0 ≤ d670 p :=
  nonnegative_ite (p 113) (nonnegative669 p) (nonnegative667 p)
def d671 (p : Pattern) : Int := if p 112 then d670 p else d665 p
theorem agree671 (p q : Pattern) (h : Agree support p q) : d671 p = d671 q := by
  simp only [d671, h 112 (by decide), agree670 p q h, agree665 p q h]
theorem nonnegative671 (p : Pattern) : 0 ≤ d671 p :=
  nonnegative_ite (p 112) (nonnegative670 p) (nonnegative665 p)
def d672 (p : Pattern) : Int := if p 106 then d671 p else d658 p
theorem agree672 (p q : Pattern) (h : Agree support p q) : d672 p = d672 q := by
  simp only [d672, h 106 (by decide), agree671 p q h, agree658 p q h]
theorem nonnegative672 (p : Pattern) : 0 ≤ d672 p :=
  nonnegative_ite (p 106) (nonnegative671 p) (nonnegative658 p)
def d673 (p : Pattern) : Int := if p 138 then d655 p else d7 p
theorem agree673 (p q : Pattern) (h : Agree support p q) : d673 p = d673 q := by
  simp only [d673, h 138 (by decide), agree655 p q h, agree7 p q h]
theorem nonnegative673 (p : Pattern) : 0 ≤ d673 p :=
  nonnegative_ite (p 138) (nonnegative655 p) (nonnegative7 p)
def d674 (p : Pattern) : Int := if p 113 then d673 p else d654 p
theorem agree674 (p q : Pattern) (h : Agree support p q) : d674 p = d674 q := by
  simp only [d674, h 113 (by decide), agree673 p q h, agree654 p q h]
theorem nonnegative674 (p : Pattern) : 0 ≤ d674 p :=
  nonnegative_ite (p 113) (nonnegative673 p) (nonnegative654 p)
def d675 (p : Pattern) : Int := if p 112 then d660 p else d674 p
theorem agree675 (p q : Pattern) (h : Agree support p q) : d675 p = d675 q := by
  simp only [d675, h 112 (by decide), agree660 p q h, agree674 p q h]
theorem nonnegative675 (p : Pattern) : 0 ≤ d675 p :=
  nonnegative_ite (p 112) (nonnegative660 p) (nonnegative674 p)
def d676 (p : Pattern) : Int := if p 133 then d659 p else d673 p
theorem agree676 (p q : Pattern) (h : Agree support p q) : d676 p = d676 q := by
  simp only [d676, h 133 (by decide), agree659 p q h, agree673 p q h]
theorem nonnegative676 (p : Pattern) : 0 ≤ d676 p :=
  nonnegative_ite (p 133) (nonnegative659 p) (nonnegative673 p)
def d677 (p : Pattern) : Int := if p 132 then d676 p else d673 p
theorem agree677 (p q : Pattern) (h : Agree support p q) : d677 p = d677 q := by
  simp only [d677, h 132 (by decide), agree676 p q h, agree673 p q h]
theorem nonnegative677 (p : Pattern) : 0 ≤ d677 p :=
  nonnegative_ite (p 132) (nonnegative676 p) (nonnegative673 p)
def d678 (p : Pattern) : Int := if p 113 then d677 p else d664 p
theorem agree678 (p q : Pattern) (h : Agree support p q) : d678 p = d678 q := by
  simp only [d678, h 113 (by decide), agree677 p q h, agree664 p q h]
theorem nonnegative678 (p : Pattern) : 0 ≤ d678 p :=
  nonnegative_ite (p 113) (nonnegative677 p) (nonnegative664 p)
def d679 (p : Pattern) : Int := if p 133 then d2 p else d660 p
theorem agree679 (p q : Pattern) (h : Agree support p q) : d679 p = d679 q := by
  simp only [d679, h 133 (by decide), agree2 p q h, agree660 p q h]
theorem nonnegative679 (p : Pattern) : 0 ≤ d679 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative660 p)
def d680 (p : Pattern) : Int := if p 132 then d679 p else d660 p
theorem agree680 (p q : Pattern) (h : Agree support p q) : d680 p = d680 q := by
  simp only [d680, h 132 (by decide), agree679 p q h, agree660 p q h]
theorem nonnegative680 (p : Pattern) : 0 ≤ d680 p :=
  nonnegative_ite (p 132) (nonnegative679 p) (nonnegative660 p)
def d681 (p : Pattern) : Int := if p 133 then d2 p else d659 p
theorem agree681 (p q : Pattern) (h : Agree support p q) : d681 p = d681 q := by
  simp only [d681, h 133 (by decide), agree2 p q h, agree659 p q h]
theorem nonnegative681 (p : Pattern) : 0 ≤ d681 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative659 p)
def d682 (p : Pattern) : Int := if p 132 then d681 p else d659 p
theorem agree682 (p q : Pattern) (h : Agree support p q) : d682 p = d682 q := by
  simp only [d682, h 132 (by decide), agree681 p q h, agree659 p q h]
theorem nonnegative682 (p : Pattern) : 0 ≤ d682 p :=
  nonnegative_ite (p 132) (nonnegative681 p) (nonnegative659 p)
def d683 (p : Pattern) : Int := if p 113 then d682 p else d680 p
theorem agree683 (p q : Pattern) (h : Agree support p q) : d683 p = d683 q := by
  simp only [d683, h 113 (by decide), agree682 p q h, agree680 p q h]
theorem nonnegative683 (p : Pattern) : 0 ≤ d683 p :=
  nonnegative_ite (p 113) (nonnegative682 p) (nonnegative680 p)
def d684 (p : Pattern) : Int := if p 112 then d683 p else d678 p
theorem agree684 (p q : Pattern) (h : Agree support p q) : d684 p = d684 q := by
  simp only [d684, h 112 (by decide), agree683 p q h, agree678 p q h]
theorem nonnegative684 (p : Pattern) : 0 ≤ d684 p :=
  nonnegative_ite (p 112) (nonnegative683 p) (nonnegative678 p)
def d685 (p : Pattern) : Int := if p 106 then d684 p else d675 p
theorem agree685 (p q : Pattern) (h : Agree support p q) : d685 p = d685 q := by
  simp only [d685, h 106 (by decide), agree684 p q h, agree675 p q h]
theorem nonnegative685 (p : Pattern) : 0 ≤ d685 p :=
  nonnegative_ite (p 106) (nonnegative684 p) (nonnegative675 p)
def d686 (p : Pattern) : Int := if p 86 then d685 p else d672 p
theorem agree686 (p q : Pattern) (h : Agree support p q) : d686 p = d686 q := by
  simp only [d686, h 86 (by decide), agree685 p q h, agree672 p q h]
theorem nonnegative686 (p : Pattern) : 0 ≤ d686 p :=
  nonnegative_ite (p 86) (nonnegative685 p) (nonnegative672 p)
def d687 (p : Pattern) : Int := if p 112 then d670 p else d664 p
theorem agree687 (p q : Pattern) (h : Agree support p q) : d687 p = d687 q := by
  simp only [d687, h 112 (by decide), agree670 p q h, agree664 p q h]
theorem nonnegative687 (p : Pattern) : 0 ≤ d687 p :=
  nonnegative_ite (p 112) (nonnegative670 p) (nonnegative664 p)
def d688 (p : Pattern) : Int := if p 106 then d687 p else d658 p
theorem agree688 (p q : Pattern) (h : Agree support p q) : d688 p = d688 q := by
  simp only [d688, h 106 (by decide), agree687 p q h, agree658 p q h]
theorem nonnegative688 (p : Pattern) : 0 ≤ d688 p :=
  nonnegative_ite (p 106) (nonnegative687 p) (nonnegative658 p)
def d689 (p : Pattern) : Int := if p 113 then d659 p else d660 p
theorem agree689 (p q : Pattern) (h : Agree support p q) : d689 p = d689 q := by
  simp only [d689, h 113 (by decide), agree659 p q h, agree660 p q h]
theorem nonnegative689 (p : Pattern) : 0 ≤ d689 p :=
  nonnegative_ite (p 113) (nonnegative659 p) (nonnegative660 p)
def d690 (p : Pattern) : Int := if p 112 then d689 p else d674 p
theorem agree690 (p q : Pattern) (h : Agree support p q) : d690 p = d690 q := by
  simp only [d690, h 112 (by decide), agree689 p q h, agree674 p q h]
theorem nonnegative690 (p : Pattern) : 0 ≤ d690 p :=
  nonnegative_ite (p 112) (nonnegative689 p) (nonnegative674 p)
def d691 (p : Pattern) : Int := if p 113 then d669 p else d664 p
theorem agree691 (p q : Pattern) (h : Agree support p q) : d691 p = d691 q := by
  simp only [d691, h 113 (by decide), agree669 p q h, agree664 p q h]
theorem nonnegative691 (p : Pattern) : 0 ≤ d691 p :=
  nonnegative_ite (p 113) (nonnegative669 p) (nonnegative664 p)
def d692 (p : Pattern) : Int := if p 113 then d2 p else d682 p
theorem agree692 (p q : Pattern) (h : Agree support p q) : d692 p = d692 q := by
  simp only [d692, h 113 (by decide), agree2 p q h, agree682 p q h]
theorem nonnegative692 (p : Pattern) : 0 ≤ d692 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative682 p)
def d693 (p : Pattern) : Int := if p 112 then d692 p else d691 p
theorem agree693 (p q : Pattern) (h : Agree support p q) : d693 p = d693 q := by
  simp only [d693, h 112 (by decide), agree692 p q h, agree691 p q h]
theorem nonnegative693 (p : Pattern) : 0 ≤ d693 p :=
  nonnegative_ite (p 112) (nonnegative692 p) (nonnegative691 p)
def d694 (p : Pattern) : Int := if p 106 then d693 p else d690 p
theorem agree694 (p q : Pattern) (h : Agree support p q) : d694 p = d694 q := by
  simp only [d694, h 106 (by decide), agree693 p q h, agree690 p q h]
theorem nonnegative694 (p : Pattern) : 0 ≤ d694 p :=
  nonnegative_ite (p 106) (nonnegative693 p) (nonnegative690 p)
def d695 (p : Pattern) : Int := if p 86 then d694 p else d688 p
theorem agree695 (p q : Pattern) (h : Agree support p q) : d695 p = d695 q := by
  simp only [d695, h 86 (by decide), agree694 p q h, agree688 p q h]
theorem nonnegative695 (p : Pattern) : 0 ≤ d695 p :=
  nonnegative_ite (p 86) (nonnegative694 p) (nonnegative688 p)
def d696 (p : Pattern) : Int := if p 80 then d695 p else d686 p
theorem agree696 (p q : Pattern) (h : Agree support p q) : d696 p = d696 q := by
  simp only [d696, h 80 (by decide), agree695 p q h, agree686 p q h]
theorem nonnegative696 (p : Pattern) : 0 ≤ d696 p :=
  nonnegative_ite (p 80) (nonnegative695 p) (nonnegative686 p)
def d697 (p : Pattern) : Int := if p 158 then d37 p else d5 p
theorem agree697 (p q : Pattern) (h : Agree support p q) : d697 p = d697 q := by
  simp only [d697, h 158 (by decide), agree37 p q h, agree5 p q h]
theorem nonnegative697 (p : Pattern) : 0 ≤ d697 p :=
  nonnegative_ite (p 158) (nonnegative37 p) (nonnegative5 p)
def d698 (p : Pattern) : Int := if p 158 then d39 p else d11 p
theorem agree698 (p q : Pattern) (h : Agree support p q) : d698 p = d698 q := by
  simp only [d698, h 158 (by decide), agree39 p q h, agree11 p q h]
theorem nonnegative698 (p : Pattern) : 0 ≤ d698 p :=
  nonnegative_ite (p 158) (nonnegative39 p) (nonnegative11 p)
def d699 (p : Pattern) : Int := if p 139 then d698 p else d697 p
theorem agree699 (p q : Pattern) (h : Agree support p q) : d699 p = d699 q := by
  simp only [d699, h 139 (by decide), agree698 p q h, agree697 p q h]
theorem nonnegative699 (p : Pattern) : 0 ≤ d699 p :=
  nonnegative_ite (p 139) (nonnegative698 p) (nonnegative697 p)
def d700 (p : Pattern) : Int := if p 138 then d699 p else d697 p
theorem agree700 (p q : Pattern) (h : Agree support p q) : d700 p = d700 q := by
  simp only [d700, h 138 (by decide), agree699 p q h, agree697 p q h]
theorem nonnegative700 (p : Pattern) : 0 ≤ d700 p :=
  nonnegative_ite (p 138) (nonnegative699 p) (nonnegative697 p)
def d701 (p : Pattern) : Int := if p 139 then d2 p else d697 p
theorem agree701 (p q : Pattern) (h : Agree support p q) : d701 p = d701 q := by
  simp only [d701, h 139 (by decide), agree2 p q h, agree697 p q h]
theorem nonnegative701 (p : Pattern) : 0 ≤ d701 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative697 p)
def d702 (p : Pattern) : Int := if p 138 then d701 p else d699 p
theorem agree702 (p q : Pattern) (h : Agree support p q) : d702 p = d702 q := by
  simp only [d702, h 138 (by decide), agree701 p q h, agree699 p q h]
theorem nonnegative702 (p : Pattern) : 0 ≤ d702 p :=
  nonnegative_ite (p 138) (nonnegative701 p) (nonnegative699 p)
def d703 (p : Pattern) : Int := if p 113 then d702 p else d699 p
theorem agree703 (p q : Pattern) (h : Agree support p q) : d703 p = d703 q := by
  simp only [d703, h 113 (by decide), agree702 p q h, agree699 p q h]
theorem nonnegative703 (p : Pattern) : 0 ≤ d703 p :=
  nonnegative_ite (p 113) (nonnegative702 p) (nonnegative699 p)
def d704 (p : Pattern) : Int := if p 112 then d703 p else d700 p
theorem agree704 (p q : Pattern) (h : Agree support p q) : d704 p = d704 q := by
  simp only [d704, h 112 (by decide), agree703 p q h, agree700 p q h]
theorem nonnegative704 (p : Pattern) : 0 ≤ d704 p :=
  nonnegative_ite (p 112) (nonnegative703 p) (nonnegative700 p)
def d705 (p : Pattern) : Int := if p 139 then d2 p else d698 p
theorem agree705 (p q : Pattern) (h : Agree support p q) : d705 p = d705 q := by
  simp only [d705, h 139 (by decide), agree2 p q h, agree698 p q h]
theorem nonnegative705 (p : Pattern) : 0 ≤ d705 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative698 p)
def d706 (p : Pattern) : Int := if p 138 then d705 p else d698 p
theorem agree706 (p q : Pattern) (h : Agree support p q) : d706 p = d706 q := by
  simp only [d706, h 138 (by decide), agree705 p q h, agree698 p q h]
theorem nonnegative706 (p : Pattern) : 0 ≤ d706 p :=
  nonnegative_ite (p 138) (nonnegative705 p) (nonnegative698 p)
def d707 (p : Pattern) : Int := if p 133 then d706 p else d700 p
theorem agree707 (p q : Pattern) (h : Agree support p q) : d707 p = d707 q := by
  simp only [d707, h 133 (by decide), agree706 p q h, agree700 p q h]
theorem nonnegative707 (p : Pattern) : 0 ≤ d707 p :=
  nonnegative_ite (p 133) (nonnegative706 p) (nonnegative700 p)
def d708 (p : Pattern) : Int := if p 132 then d707 p else d700 p
theorem agree708 (p q : Pattern) (h : Agree support p q) : d708 p = d708 q := by
  simp only [d708, h 132 (by decide), agree707 p q h, agree700 p q h]
theorem nonnegative708 (p : Pattern) : 0 ≤ d708 p :=
  nonnegative_ite (p 132) (nonnegative707 p) (nonnegative700 p)
def d709 (p : Pattern) : Int := if p 133 then d705 p else d700 p
theorem agree709 (p q : Pattern) (h : Agree support p q) : d709 p = d709 q := by
  simp only [d709, h 133 (by decide), agree705 p q h, agree700 p q h]
theorem nonnegative709 (p : Pattern) : 0 ≤ d709 p :=
  nonnegative_ite (p 133) (nonnegative705 p) (nonnegative700 p)
def d710 (p : Pattern) : Int := if p 132 then d709 p else d700 p
theorem agree710 (p q : Pattern) (h : Agree support p q) : d710 p = d710 q := by
  simp only [d710, h 132 (by decide), agree709 p q h, agree700 p q h]
theorem nonnegative710 (p : Pattern) : 0 ≤ d710 p :=
  nonnegative_ite (p 132) (nonnegative709 p) (nonnegative700 p)
def d711 (p : Pattern) : Int := if p 113 then d710 p else d708 p
theorem agree711 (p q : Pattern) (h : Agree support p q) : d711 p = d711 q := by
  simp only [d711, h 113 (by decide), agree710 p q h, agree708 p q h]
theorem nonnegative711 (p : Pattern) : 0 ≤ d711 p :=
  nonnegative_ite (p 113) (nonnegative710 p) (nonnegative708 p)
def d712 (p : Pattern) : Int := if p 133 then d705 p else d699 p
theorem agree712 (p q : Pattern) (h : Agree support p q) : d712 p = d712 q := by
  simp only [d712, h 133 (by decide), agree705 p q h, agree699 p q h]
theorem nonnegative712 (p : Pattern) : 0 ≤ d712 p :=
  nonnegative_ite (p 133) (nonnegative705 p) (nonnegative699 p)
def d713 (p : Pattern) : Int := if p 132 then d712 p else d699 p
theorem agree713 (p q : Pattern) (h : Agree support p q) : d713 p = d713 q := by
  simp only [d713, h 132 (by decide), agree712 p q h, agree699 p q h]
theorem nonnegative713 (p : Pattern) : 0 ≤ d713 p :=
  nonnegative_ite (p 132) (nonnegative712 p) (nonnegative699 p)
def d714 (p : Pattern) : Int := if p 133 then d705 p else d702 p
theorem agree714 (p q : Pattern) (h : Agree support p q) : d714 p = d714 q := by
  simp only [d714, h 133 (by decide), agree705 p q h, agree702 p q h]
theorem nonnegative714 (p : Pattern) : 0 ≤ d714 p :=
  nonnegative_ite (p 133) (nonnegative705 p) (nonnegative702 p)
def d715 (p : Pattern) : Int := if p 132 then d714 p else d702 p
theorem agree715 (p q : Pattern) (h : Agree support p q) : d715 p = d715 q := by
  simp only [d715, h 132 (by decide), agree714 p q h, agree702 p q h]
theorem nonnegative715 (p : Pattern) : 0 ≤ d715 p :=
  nonnegative_ite (p 132) (nonnegative714 p) (nonnegative702 p)
def d716 (p : Pattern) : Int := if p 113 then d715 p else d713 p
theorem agree716 (p q : Pattern) (h : Agree support p q) : d716 p = d716 q := by
  simp only [d716, h 113 (by decide), agree715 p q h, agree713 p q h]
theorem nonnegative716 (p : Pattern) : 0 ≤ d716 p :=
  nonnegative_ite (p 113) (nonnegative715 p) (nonnegative713 p)
def d717 (p : Pattern) : Int := if p 112 then d716 p else d711 p
theorem agree717 (p q : Pattern) (h : Agree support p q) : d717 p = d717 q := by
  simp only [d717, h 112 (by decide), agree716 p q h, agree711 p q h]
theorem nonnegative717 (p : Pattern) : 0 ≤ d717 p :=
  nonnegative_ite (p 112) (nonnegative716 p) (nonnegative711 p)
def d718 (p : Pattern) : Int := if p 106 then d717 p else d704 p
theorem agree718 (p q : Pattern) (h : Agree support p q) : d718 p = d718 q := by
  simp only [d718, h 106 (by decide), agree717 p q h, agree704 p q h]
theorem nonnegative718 (p : Pattern) : 0 ≤ d718 p :=
  nonnegative_ite (p 106) (nonnegative717 p) (nonnegative704 p)
def d719 (p : Pattern) : Int := if p 138 then d701 p else d697 p
theorem agree719 (p q : Pattern) (h : Agree support p q) : d719 p = d719 q := by
  simp only [d719, h 138 (by decide), agree701 p q h, agree697 p q h]
theorem nonnegative719 (p : Pattern) : 0 ≤ d719 p :=
  nonnegative_ite (p 138) (nonnegative701 p) (nonnegative697 p)
end NetHack.Sokoban32Refined
