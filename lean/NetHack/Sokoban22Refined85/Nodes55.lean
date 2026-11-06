/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes54
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6600 (p : Pattern) : Int := if p 225 then d6599 p else d6598 p
theorem agree6600 (p q : Pattern) (h : Agree support p q) : d6600 p = d6600 q := by
  simp only [d6600, h 225 (by decide), agree6599 p q h, agree6598 p q h]
theorem nonnegative6600 (p : Pattern) : 0 ≤ d6600 p :=
  nonnegative_ite (p 225) (nonnegative6599 p) (nonnegative6598 p)
def d6601 (p : Pattern) : Int := if p 224 then d6600 p else d6597 p
theorem agree6601 (p q : Pattern) (h : Agree support p q) : d6601 p = d6601 q := by
  simp only [d6601, h 224 (by decide), agree6600 p q h, agree6597 p q h]
theorem nonnegative6601 (p : Pattern) : 0 ≤ d6601 p :=
  nonnegative_ite (p 224) (nonnegative6600 p) (nonnegative6597 p)
def d6602 (p : Pattern) : Int := if p 204 then d12 p else d6601 p
theorem agree6602 (p q : Pattern) (h : Agree support p q) : d6602 p = d6602 q := by
  simp only [d6602, h 204 (by decide), agree12 p q h, agree6601 p q h]
theorem nonnegative6602 (p : Pattern) : 0 ≤ d6602 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6601 p)
def d6603 (p : Pattern) : Int := if p 182 then d6602 p else d6595 p
theorem agree6603 (p q : Pattern) (h : Agree support p q) : d6603 p = d6603 q := by
  simp only [d6603, h 182 (by decide), agree6602 p q h, agree6595 p q h]
theorem nonnegative6603 (p : Pattern) : 0 ≤ d6603 p :=
  nonnegative_ite (p 182) (nonnegative6602 p) (nonnegative6595 p)
def d6604 (p : Pattern) : Int := if p 225 then d3253 p else d6 p
theorem agree6604 (p q : Pattern) (h : Agree support p q) : d6604 p = d6604 q := by
  simp only [d6604, h 225 (by decide), agree3253 p q h, agree6 p q h]
theorem nonnegative6604 (p : Pattern) : 0 ≤ d6604 p :=
  nonnegative_ite (p 225) (nonnegative3253 p) (nonnegative6 p)
def d6605 (p : Pattern) : Int := if p 246 then d10 p else d6 p
theorem agree6605 (p q : Pattern) (h : Agree support p q) : d6605 p = d6605 q := by
  simp only [d6605, h 246 (by decide), agree10 p q h, agree6 p q h]
theorem nonnegative6605 (p : Pattern) : 0 ≤ d6605 p :=
  nonnegative_ite (p 246) (nonnegative10 p) (nonnegative6 p)
def d6606 (p : Pattern) : Int := if p 225 then d3253 p else d6605 p
theorem agree6606 (p q : Pattern) (h : Agree support p q) : d6606 p = d6606 q := by
  simp only [d6606, h 225 (by decide), agree3253 p q h, agree6605 p q h]
theorem nonnegative6606 (p : Pattern) : 0 ≤ d6606 p :=
  nonnegative_ite (p 225) (nonnegative3253 p) (nonnegative6605 p)
def d6607 (p : Pattern) : Int := if p 224 then d6606 p else d6604 p
theorem agree6607 (p q : Pattern) (h : Agree support p q) : d6607 p = d6607 q := by
  simp only [d6607, h 224 (by decide), agree6606 p q h, agree6604 p q h]
theorem nonnegative6607 (p : Pattern) : 0 ≤ d6607 p :=
  nonnegative_ite (p 224) (nonnegative6606 p) (nonnegative6604 p)
def d6608 (p : Pattern) : Int := if p 204 then d12 p else d6607 p
theorem agree6608 (p q : Pattern) (h : Agree support p q) : d6608 p = d6608 q := by
  simp only [d6608, h 204 (by decide), agree12 p q h, agree6607 p q h]
theorem nonnegative6608 (p : Pattern) : 0 ≤ d6608 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6607 p)
def d6609 (p : Pattern) : Int := if p 182 then d6608 p else d6595 p
theorem agree6609 (p q : Pattern) (h : Agree support p q) : d6609 p = d6609 q := by
  simp only [d6609, h 182 (by decide), agree6608 p q h, agree6595 p q h]
theorem nonnegative6609 (p : Pattern) : 0 ≤ d6609 p :=
  nonnegative_ite (p 182) (nonnegative6608 p) (nonnegative6595 p)
def d6610 (p : Pattern) : Int := if p 163 then d6609 p else d6603 p
theorem agree6610 (p q : Pattern) (h : Agree support p q) : d6610 p = d6610 q := by
  simp only [d6610, h 163 (by decide), agree6609 p q h, agree6603 p q h]
theorem nonnegative6610 (p : Pattern) : 0 ≤ d6610 p :=
  nonnegative_ite (p 163) (nonnegative6609 p) (nonnegative6603 p)
def d6611 (p : Pattern) : Int := if p 225 then d3257 p else d11 p
theorem agree6611 (p q : Pattern) (h : Agree support p q) : d6611 p = d6611 q := by
  simp only [d6611, h 225 (by decide), agree3257 p q h, agree11 p q h]
theorem nonnegative6611 (p : Pattern) : 0 ≤ d6611 p :=
  nonnegative_ite (p 225) (nonnegative3257 p) (nonnegative11 p)
def d6612 (p : Pattern) : Int := if p 224 then d3257 p else d6611 p
theorem agree6612 (p q : Pattern) (h : Agree support p q) : d6612 p = d6612 q := by
  simp only [d6612, h 224 (by decide), agree3257 p q h, agree6611 p q h]
theorem nonnegative6612 (p : Pattern) : 0 ≤ d6612 p :=
  nonnegative_ite (p 224) (nonnegative3257 p) (nonnegative6611 p)
def d6613 (p : Pattern) : Int := if p 204 then d12 p else d6612 p
theorem agree6613 (p q : Pattern) (h : Agree support p q) : d6613 p = d6613 q := by
  simp only [d6613, h 204 (by decide), agree12 p q h, agree6612 p q h]
theorem nonnegative6613 (p : Pattern) : 0 ≤ d6613 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6612 p)
def d6614 (p : Pattern) : Int := if p 182 then d6613 p else d6595 p
theorem agree6614 (p q : Pattern) (h : Agree support p q) : d6614 p = d6614 q := by
  simp only [d6614, h 182 (by decide), agree6613 p q h, agree6595 p q h]
theorem nonnegative6614 (p : Pattern) : 0 ≤ d6614 p :=
  nonnegative_ite (p 182) (nonnegative6613 p) (nonnegative6595 p)
def d6615 (p : Pattern) : Int := if p 246 then d10 p else d4 p
theorem agree6615 (p q : Pattern) (h : Agree support p q) : d6615 p = d6615 q := by
  simp only [d6615, h 246 (by decide), agree10 p q h, agree4 p q h]
theorem nonnegative6615 (p : Pattern) : 0 ≤ d6615 p :=
  nonnegative_ite (p 246) (nonnegative10 p) (nonnegative4 p)
def d6616 (p : Pattern) : Int := if p 225 then d6615 p else d4 p
theorem agree6616 (p q : Pattern) (h : Agree support p q) : d6616 p = d6616 q := by
  simp only [d6616, h 225 (by decide), agree6615 p q h, agree4 p q h]
theorem nonnegative6616 (p : Pattern) : 0 ≤ d6616 p :=
  nonnegative_ite (p 225) (nonnegative6615 p) (nonnegative4 p)
def d6617 (p : Pattern) : Int := if p 225 then d3239 p else d6568 p
theorem agree6617 (p q : Pattern) (h : Agree support p q) : d6617 p = d6617 q := by
  simp only [d6617, h 225 (by decide), agree3239 p q h, agree6568 p q h]
theorem nonnegative6617 (p : Pattern) : 0 ≤ d6617 p :=
  nonnegative_ite (p 225) (nonnegative3239 p) (nonnegative6568 p)
def d6618 (p : Pattern) : Int := if p 224 then d6617 p else d6616 p
theorem agree6618 (p q : Pattern) (h : Agree support p q) : d6618 p = d6618 q := by
  simp only [d6618, h 224 (by decide), agree6617 p q h, agree6616 p q h]
theorem nonnegative6618 (p : Pattern) : 0 ≤ d6618 p :=
  nonnegative_ite (p 224) (nonnegative6617 p) (nonnegative6616 p)
def d6619 (p : Pattern) : Int := if p 204 then d6618 p else d4 p
theorem agree6619 (p q : Pattern) (h : Agree support p q) : d6619 p = d6619 q := by
  simp only [d6619, h 204 (by decide), agree6618 p q h, agree4 p q h]
theorem nonnegative6619 (p : Pattern) : 0 ≤ d6619 p :=
  nonnegative_ite (p 204) (nonnegative6618 p) (nonnegative4 p)
def d6620 (p : Pattern) : Int := if p 182 then d12 p else d6619 p
theorem agree6620 (p q : Pattern) (h : Agree support p q) : d6620 p = d6620 q := by
  simp only [d6620, h 182 (by decide), agree12 p q h, agree6619 p q h]
theorem nonnegative6620 (p : Pattern) : 0 ≤ d6620 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6619 p)
def d6621 (p : Pattern) : Int := if p 163 then d6620 p else d6614 p
theorem agree6621 (p q : Pattern) (h : Agree support p q) : d6621 p = d6621 q := by
  simp only [d6621, h 163 (by decide), agree6620 p q h, agree6614 p q h]
theorem nonnegative6621 (p : Pattern) : 0 ≤ d6621 p :=
  nonnegative_ite (p 163) (nonnegative6620 p) (nonnegative6614 p)
def d6622 (p : Pattern) : Int := if p 162 then d6621 p else d6610 p
theorem agree6622 (p q : Pattern) (h : Agree support p q) : d6622 p = d6622 q := by
  simp only [d6622, h 162 (by decide), agree6621 p q h, agree6610 p q h]
theorem nonnegative6622 (p : Pattern) : 0 ≤ d6622 p :=
  nonnegative_ite (p 162) (nonnegative6621 p) (nonnegative6610 p)
def d6623 (p : Pattern) : Int := if p 182 then d12 p else d6595 p
theorem agree6623 (p q : Pattern) (h : Agree support p q) : d6623 p = d6623 q := by
  simp only [d6623, h 182 (by decide), agree12 p q h, agree6595 p q h]
theorem nonnegative6623 (p : Pattern) : 0 ≤ d6623 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6595 p)
def d6624 (p : Pattern) : Int := if p 163 then d6620 p else d6623 p
theorem agree6624 (p q : Pattern) (h : Agree support p q) : d6624 p = d6624 q := by
  simp only [d6624, h 163 (by decide), agree6620 p q h, agree6623 p q h]
theorem nonnegative6624 (p : Pattern) : 0 ≤ d6624 p :=
  nonnegative_ite (p 163) (nonnegative6620 p) (nonnegative6623 p)
def d6625 (p : Pattern) : Int := if p 182 then d12 p else d6581 p
theorem agree6625 (p q : Pattern) (h : Agree support p q) : d6625 p = d6625 q := by
  simp only [d6625, h 182 (by decide), agree12 p q h, agree6581 p q h]
theorem nonnegative6625 (p : Pattern) : 0 ≤ d6625 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6581 p)
def d6626 (p : Pattern) : Int := if p 163 then d12 p else d6625 p
theorem agree6626 (p q : Pattern) (h : Agree support p q) : d6626 p = d6626 q := by
  simp only [d6626, h 163 (by decide), agree12 p q h, agree6625 p q h]
theorem nonnegative6626 (p : Pattern) : 0 ≤ d6626 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6625 p)
def d6627 (p : Pattern) : Int := if p 162 then d6626 p else d6624 p
theorem agree6627 (p q : Pattern) (h : Agree support p q) : d6627 p = d6627 q := by
  simp only [d6627, h 162 (by decide), agree6626 p q h, agree6624 p q h]
theorem nonnegative6627 (p : Pattern) : 0 ≤ d6627 p :=
  nonnegative_ite (p 162) (nonnegative6626 p) (nonnegative6624 p)
def d6628 (p : Pattern) : Int := if p 161 then d6627 p else d6622 p
theorem agree6628 (p q : Pattern) (h : Agree support p q) : d6628 p = d6628 q := by
  simp only [d6628, h 161 (by decide), agree6627 p q h, agree6622 p q h]
theorem nonnegative6628 (p : Pattern) : 0 ≤ d6628 p :=
  nonnegative_ite (p 161) (nonnegative6627 p) (nonnegative6622 p)
def d6629 (p : Pattern) : Int := if p 160 then d6628 p else d6589 p
theorem agree6629 (p q : Pattern) (h : Agree support p q) : d6629 p = d6629 q := by
  simp only [d6629, h 160 (by decide), agree6628 p q h, agree6589 p q h]
theorem nonnegative6629 (p : Pattern) : 0 ≤ d6629 p :=
  nonnegative_ite (p 160) (nonnegative6628 p) (nonnegative6589 p)
def d6630 (p : Pattern) : Int := if p 225 then d6598 p else d2 p
theorem agree6630 (p q : Pattern) (h : Agree support p q) : d6630 p = d6630 q := by
  simp only [d6630, h 225 (by decide), agree6598 p q h, agree2 p q h]
theorem nonnegative6630 (p : Pattern) : 0 ≤ d6630 p :=
  nonnegative_ite (p 225) (nonnegative6598 p) (nonnegative2 p)
def d6631 (p : Pattern) : Int := if p 224 then d6598 p else d6630 p
theorem agree6631 (p q : Pattern) (h : Agree support p q) : d6631 p = d6631 q := by
  simp only [d6631, h 224 (by decide), agree6598 p q h, agree6630 p q h]
theorem nonnegative6631 (p : Pattern) : 0 ≤ d6631 p :=
  nonnegative_ite (p 224) (nonnegative6598 p) (nonnegative6630 p)
def d6632 (p : Pattern) : Int := if p 204 then d6631 p else d2 p
theorem agree6632 (p q : Pattern) (h : Agree support p q) : d6632 p = d6632 q := by
  simp only [d6632, h 204 (by decide), agree6631 p q h, agree2 p q h]
theorem nonnegative6632 (p : Pattern) : 0 ≤ d6632 p :=
  nonnegative_ite (p 204) (nonnegative6631 p) (nonnegative2 p)
def d6633 (p : Pattern) : Int := if p 246 then d4 p else d2 p
theorem agree6633 (p q : Pattern) (h : Agree support p q) : d6633 p = d6633 q := by
  simp only [d6633, h 246 (by decide), agree4 p q h, agree2 p q h]
theorem nonnegative6633 (p : Pattern) : 0 ≤ d6633 p :=
  nonnegative_ite (p 246) (nonnegative4 p) (nonnegative2 p)
def d6634 (p : Pattern) : Int := if p 225 then d6633 p else d2 p
theorem agree6634 (p q : Pattern) (h : Agree support p q) : d6634 p = d6634 q := by
  simp only [d6634, h 225 (by decide), agree6633 p q h, agree2 p q h]
theorem nonnegative6634 (p : Pattern) : 0 ≤ d6634 p :=
  nonnegative_ite (p 225) (nonnegative6633 p) (nonnegative2 p)
def d6635 (p : Pattern) : Int := if p 224 then d6633 p else d6634 p
theorem agree6635 (p q : Pattern) (h : Agree support p q) : d6635 p = d6635 q := by
  simp only [d6635, h 224 (by decide), agree6633 p q h, agree6634 p q h]
theorem nonnegative6635 (p : Pattern) : 0 ≤ d6635 p :=
  nonnegative_ite (p 224) (nonnegative6633 p) (nonnegative6634 p)
def d6636 (p : Pattern) : Int := if p 204 then d12 p else d6635 p
theorem agree6636 (p q : Pattern) (h : Agree support p q) : d6636 p = d6636 q := by
  simp only [d6636, h 204 (by decide), agree12 p q h, agree6635 p q h]
theorem nonnegative6636 (p : Pattern) : 0 ≤ d6636 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6635 p)
def d6637 (p : Pattern) : Int := if p 182 then d6636 p else d6632 p
theorem agree6637 (p q : Pattern) (h : Agree support p q) : d6637 p = d6637 q := by
  simp only [d6637, h 182 (by decide), agree6636 p q h, agree6632 p q h]
theorem nonnegative6637 (p : Pattern) : 0 ≤ d6637 p :=
  nonnegative_ite (p 182) (nonnegative6636 p) (nonnegative6632 p)
def d6638 (p : Pattern) : Int := if p 163 then d6637 p else d6567 p
theorem agree6638 (p q : Pattern) (h : Agree support p q) : d6638 p = d6638 q := by
  simp only [d6638, h 163 (by decide), agree6637 p q h, agree6567 p q h]
theorem nonnegative6638 (p : Pattern) : 0 ≤ d6638 p :=
  nonnegative_ite (p 163) (nonnegative6637 p) (nonnegative6567 p)
def d6639 (p : Pattern) : Int := if p 163 then d6586 p else d6576 p
theorem agree6639 (p q : Pattern) (h : Agree support p q) : d6639 p = d6639 q := by
  simp only [d6639, h 163 (by decide), agree6586 p q h, agree6576 p q h]
theorem nonnegative6639 (p : Pattern) : 0 ≤ d6639 p :=
  nonnegative_ite (p 163) (nonnegative6586 p) (nonnegative6576 p)
def d6640 (p : Pattern) : Int := if p 162 then d6639 p else d6638 p
theorem agree6640 (p q : Pattern) (h : Agree support p q) : d6640 p = d6640 q := by
  simp only [d6640, h 162 (by decide), agree6639 p q h, agree6638 p q h]
theorem nonnegative6640 (p : Pattern) : 0 ≤ d6640 p :=
  nonnegative_ite (p 162) (nonnegative6639 p) (nonnegative6638 p)
def d6641 (p : Pattern) : Int := if p 225 then d3279 p else d10 p
theorem agree6641 (p q : Pattern) (h : Agree support p q) : d6641 p = d6641 q := by
  simp only [d6641, h 225 (by decide), agree3279 p q h, agree10 p q h]
theorem nonnegative6641 (p : Pattern) : 0 ≤ d6641 p :=
  nonnegative_ite (p 225) (nonnegative3279 p) (nonnegative10 p)
def d6642 (p : Pattern) : Int := if p 224 then d3279 p else d6641 p
theorem agree6642 (p q : Pattern) (h : Agree support p q) : d6642 p = d6642 q := by
  simp only [d6642, h 224 (by decide), agree3279 p q h, agree6641 p q h]
theorem nonnegative6642 (p : Pattern) : 0 ≤ d6642 p :=
  nonnegative_ite (p 224) (nonnegative3279 p) (nonnegative6641 p)
def d6643 (p : Pattern) : Int := if p 204 then d6642 p else d10 p
theorem agree6643 (p q : Pattern) (h : Agree support p q) : d6643 p = d6643 q := by
  simp only [d6643, h 204 (by decide), agree6642 p q h, agree10 p q h]
theorem nonnegative6643 (p : Pattern) : 0 ≤ d6643 p :=
  nonnegative_ite (p 204) (nonnegative6642 p) (nonnegative10 p)
def d6644 (p : Pattern) : Int := if p 204 then d12 p else d6642 p
theorem agree6644 (p q : Pattern) (h : Agree support p q) : d6644 p = d6644 q := by
  simp only [d6644, h 204 (by decide), agree12 p q h, agree6642 p q h]
theorem nonnegative6644 (p : Pattern) : 0 ≤ d6644 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6642 p)
def d6645 (p : Pattern) : Int := if p 182 then d6644 p else d6643 p
theorem agree6645 (p q : Pattern) (h : Agree support p q) : d6645 p = d6645 q := by
  simp only [d6645, h 182 (by decide), agree6644 p q h, agree6643 p q h]
theorem nonnegative6645 (p : Pattern) : 0 ≤ d6645 p :=
  nonnegative_ite (p 182) (nonnegative6644 p) (nonnegative6643 p)
def d6646 (p : Pattern) : Int := if p 163 then d6645 p else d6576 p
theorem agree6646 (p q : Pattern) (h : Agree support p q) : d6646 p = d6646 q := by
  simp only [d6646, h 163 (by decide), agree6645 p q h, agree6576 p q h]
theorem nonnegative6646 (p : Pattern) : 0 ≤ d6646 p :=
  nonnegative_ite (p 163) (nonnegative6645 p) (nonnegative6576 p)
def d6647 (p : Pattern) : Int := if p 204 then d6612 p else d11 p
theorem agree6647 (p q : Pattern) (h : Agree support p q) : d6647 p = d6647 q := by
  simp only [d6647, h 204 (by decide), agree6612 p q h, agree11 p q h]
theorem nonnegative6647 (p : Pattern) : 0 ≤ d6647 p :=
  nonnegative_ite (p 204) (nonnegative6612 p) (nonnegative11 p)
def d6648 (p : Pattern) : Int := if p 182 then d6613 p else d6647 p
theorem agree6648 (p q : Pattern) (h : Agree support p q) : d6648 p = d6648 q := by
  simp only [d6648, h 182 (by decide), agree6613 p q h, agree6647 p q h]
theorem nonnegative6648 (p : Pattern) : 0 ≤ d6648 p :=
  nonnegative_ite (p 182) (nonnegative6613 p) (nonnegative6647 p)
def d6649 (p : Pattern) : Int := if p 163 then d12 p else d6648 p
theorem agree6649 (p q : Pattern) (h : Agree support p q) : d6649 p = d6649 q := by
  simp only [d6649, h 163 (by decide), agree12 p q h, agree6648 p q h]
theorem nonnegative6649 (p : Pattern) : 0 ≤ d6649 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6648 p)
def d6650 (p : Pattern) : Int := if p 162 then d6649 p else d6646 p
theorem agree6650 (p q : Pattern) (h : Agree support p q) : d6650 p = d6650 q := by
  simp only [d6650, h 162 (by decide), agree6649 p q h, agree6646 p q h]
theorem nonnegative6650 (p : Pattern) : 0 ≤ d6650 p :=
  nonnegative_ite (p 162) (nonnegative6649 p) (nonnegative6646 p)
def d6651 (p : Pattern) : Int := if p 161 then d6650 p else d6640 p
theorem agree6651 (p q : Pattern) (h : Agree support p q) : d6651 p = d6651 q := by
  simp only [d6651, h 161 (by decide), agree6650 p q h, agree6640 p q h]
theorem nonnegative6651 (p : Pattern) : 0 ≤ d6651 p :=
  nonnegative_ite (p 161) (nonnegative6650 p) (nonnegative6640 p)
def d6652 (p : Pattern) : Int := if p 204 then d6601 p else d2 p
theorem agree6652 (p q : Pattern) (h : Agree support p q) : d6652 p = d6652 q := by
  simp only [d6652, h 204 (by decide), agree6601 p q h, agree2 p q h]
theorem nonnegative6652 (p : Pattern) : 0 ≤ d6652 p :=
  nonnegative_ite (p 204) (nonnegative6601 p) (nonnegative2 p)
def d6653 (p : Pattern) : Int := if p 182 then d12 p else d6652 p
theorem agree6653 (p q : Pattern) (h : Agree support p q) : d6653 p = d6653 q := by
  simp only [d6653, h 182 (by decide), agree12 p q h, agree6652 p q h]
theorem nonnegative6653 (p : Pattern) : 0 ≤ d6653 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6652 p)
def d6654 (p : Pattern) : Int := if p 163 then d6653 p else d6609 p
theorem agree6654 (p q : Pattern) (h : Agree support p q) : d6654 p = d6654 q := by
  simp only [d6654, h 163 (by decide), agree6653 p q h, agree6609 p q h]
theorem nonnegative6654 (p : Pattern) : 0 ≤ d6654 p :=
  nonnegative_ite (p 163) (nonnegative6653 p) (nonnegative6609 p)
def d6655 (p : Pattern) : Int := if p 163 then d6625 p else d6620 p
theorem agree6655 (p q : Pattern) (h : Agree support p q) : d6655 p = d6655 q := by
  simp only [d6655, h 163 (by decide), agree6625 p q h, agree6620 p q h]
theorem nonnegative6655 (p : Pattern) : 0 ≤ d6655 p :=
  nonnegative_ite (p 163) (nonnegative6625 p) (nonnegative6620 p)
def d6656 (p : Pattern) : Int := if p 162 then d6655 p else d6654 p
theorem agree6656 (p q : Pattern) (h : Agree support p q) : d6656 p = d6656 q := by
  simp only [d6656, h 162 (by decide), agree6655 p q h, agree6654 p q h]
theorem nonnegative6656 (p : Pattern) : 0 ≤ d6656 p :=
  nonnegative_ite (p 162) (nonnegative6655 p) (nonnegative6654 p)
def d6657 (p : Pattern) : Int := if p 182 then d12 p else d6643 p
theorem agree6657 (p q : Pattern) (h : Agree support p q) : d6657 p = d6657 q := by
  simp only [d6657, h 182 (by decide), agree12 p q h, agree6643 p q h]
theorem nonnegative6657 (p : Pattern) : 0 ≤ d6657 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6643 p)
def d6658 (p : Pattern) : Int := if p 163 then d6657 p else d6620 p
theorem agree6658 (p q : Pattern) (h : Agree support p q) : d6658 p = d6658 q := by
  simp only [d6658, h 163 (by decide), agree6657 p q h, agree6620 p q h]
theorem nonnegative6658 (p : Pattern) : 0 ≤ d6658 p :=
  nonnegative_ite (p 163) (nonnegative6657 p) (nonnegative6620 p)
def d6659 (p : Pattern) : Int := if p 182 then d12 p else d6647 p
theorem agree6659 (p q : Pattern) (h : Agree support p q) : d6659 p = d6659 q := by
  simp only [d6659, h 182 (by decide), agree12 p q h, agree6647 p q h]
theorem nonnegative6659 (p : Pattern) : 0 ≤ d6659 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6647 p)
def d6660 (p : Pattern) : Int := if p 163 then d12 p else d6659 p
theorem agree6660 (p q : Pattern) (h : Agree support p q) : d6660 p = d6660 q := by
  simp only [d6660, h 163 (by decide), agree12 p q h, agree6659 p q h]
theorem nonnegative6660 (p : Pattern) : 0 ≤ d6660 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6659 p)
def d6661 (p : Pattern) : Int := if p 162 then d6660 p else d6658 p
theorem agree6661 (p q : Pattern) (h : Agree support p q) : d6661 p = d6661 q := by
  simp only [d6661, h 162 (by decide), agree6660 p q h, agree6658 p q h]
theorem nonnegative6661 (p : Pattern) : 0 ≤ d6661 p :=
  nonnegative_ite (p 162) (nonnegative6660 p) (nonnegative6658 p)
def d6662 (p : Pattern) : Int := if p 161 then d6661 p else d6656 p
theorem agree6662 (p q : Pattern) (h : Agree support p q) : d6662 p = d6662 q := by
  simp only [d6662, h 161 (by decide), agree6661 p q h, agree6656 p q h]
theorem nonnegative6662 (p : Pattern) : 0 ≤ d6662 p :=
  nonnegative_ite (p 161) (nonnegative6661 p) (nonnegative6656 p)
def d6663 (p : Pattern) : Int := if p 160 then d6662 p else d6651 p
theorem agree6663 (p q : Pattern) (h : Agree support p q) : d6663 p = d6663 q := by
  simp only [d6663, h 160 (by decide), agree6662 p q h, agree6651 p q h]
theorem nonnegative6663 (p : Pattern) : 0 ≤ d6663 p :=
  nonnegative_ite (p 160) (nonnegative6662 p) (nonnegative6651 p)
def d6664 (p : Pattern) : Int := if p 141 then d6663 p else d6629 p
theorem agree6664 (p q : Pattern) (h : Agree support p q) : d6664 p = d6664 q := by
  simp only [d6664, h 141 (by decide), agree6663 p q h, agree6629 p q h]
theorem nonnegative6664 (p : Pattern) : 0 ≤ d6664 p :=
  nonnegative_ite (p 141) (nonnegative6663 p) (nonnegative6629 p)
def d6665 (p : Pattern) : Int := if p 225 then d6590 p else d6559 p
theorem agree6665 (p q : Pattern) (h : Agree support p q) : d6665 p = d6665 q := by
  simp only [d6665, h 225 (by decide), agree6590 p q h, agree6559 p q h]
theorem nonnegative6665 (p : Pattern) : 0 ≤ d6665 p :=
  nonnegative_ite (p 225) (nonnegative6590 p) (nonnegative6559 p)
def d6666 (p : Pattern) : Int := if p 224 then d6665 p else d6591 p
theorem agree6666 (p q : Pattern) (h : Agree support p q) : d6666 p = d6666 q := by
  simp only [d6666, h 224 (by decide), agree6665 p q h, agree6591 p q h]
theorem nonnegative6666 (p : Pattern) : 0 ≤ d6666 p :=
  nonnegative_ite (p 224) (nonnegative6665 p) (nonnegative6591 p)
def d6667 (p : Pattern) : Int := if p 204 then d6666 p else d0 p
theorem agree6667 (p q : Pattern) (h : Agree support p q) : d6667 p = d6667 q := by
  simp only [d6667, h 204 (by decide), agree6666 p q h, agree0 p q h]
theorem nonnegative6667 (p : Pattern) : 0 ≤ d6667 p :=
  nonnegative_ite (p 204) (nonnegative6666 p) (nonnegative0 p)
def d6668 (p : Pattern) : Int := if p 204 then d12 p else d6561 p
theorem agree6668 (p q : Pattern) (h : Agree support p q) : d6668 p = d6668 q := by
  simp only [d6668, h 204 (by decide), agree12 p q h, agree6561 p q h]
theorem nonnegative6668 (p : Pattern) : 0 ≤ d6668 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6561 p)
def d6669 (p : Pattern) : Int := if p 182 then d6668 p else d6667 p
theorem agree6669 (p q : Pattern) (h : Agree support p q) : d6669 p = d6669 q := by
  simp only [d6669, h 182 (by decide), agree6668 p q h, agree6667 p q h]
theorem nonnegative6669 (p : Pattern) : 0 ≤ d6669 p :=
  nonnegative_ite (p 182) (nonnegative6668 p) (nonnegative6667 p)
def d6670 (p : Pattern) : Int := if p 246 then d8 p else d0 p
theorem agree6670 (p q : Pattern) (h : Agree support p q) : d6670 p = d6670 q := by
  simp only [d6670, h 246 (by decide), agree8 p q h, agree0 p q h]
theorem nonnegative6670 (p : Pattern) : 0 ≤ d6670 p :=
  nonnegative_ite (p 246) (nonnegative8 p) (nonnegative0 p)
def d6671 (p : Pattern) : Int := if p 225 then d6670 p else d6559 p
theorem agree6671 (p q : Pattern) (h : Agree support p q) : d6671 p = d6671 q := by
  simp only [d6671, h 225 (by decide), agree6670 p q h, agree6559 p q h]
theorem nonnegative6671 (p : Pattern) : 0 ≤ d6671 p :=
  nonnegative_ite (p 225) (nonnegative6670 p) (nonnegative6559 p)
def d6672 (p : Pattern) : Int := if p 224 then d6671 p else d6591 p
theorem agree6672 (p q : Pattern) (h : Agree support p q) : d6672 p = d6672 q := by
  simp only [d6672, h 224 (by decide), agree6671 p q h, agree6591 p q h]
theorem nonnegative6672 (p : Pattern) : 0 ≤ d6672 p :=
  nonnegative_ite (p 224) (nonnegative6671 p) (nonnegative6591 p)
def d6673 (p : Pattern) : Int := if p 204 then d12 p else d6672 p
theorem agree6673 (p q : Pattern) (h : Agree support p q) : d6673 p = d6673 q := by
  simp only [d6673, h 204 (by decide), agree12 p q h, agree6672 p q h]
theorem nonnegative6673 (p : Pattern) : 0 ≤ d6673 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6672 p)
def d6674 (p : Pattern) : Int := if p 182 then d6673 p else d6595 p
theorem agree6674 (p q : Pattern) (h : Agree support p q) : d6674 p = d6674 q := by
  simp only [d6674, h 182 (by decide), agree6673 p q h, agree6595 p q h]
theorem nonnegative6674 (p : Pattern) : 0 ≤ d6674 p :=
  nonnegative_ite (p 182) (nonnegative6673 p) (nonnegative6595 p)
def d6675 (p : Pattern) : Int := if p 163 then d6674 p else d6669 p
theorem agree6675 (p q : Pattern) (h : Agree support p q) : d6675 p = d6675 q := by
  simp only [d6675, h 163 (by decide), agree6674 p q h, agree6669 p q h]
theorem nonnegative6675 (p : Pattern) : 0 ≤ d6675 p :=
  nonnegative_ite (p 163) (nonnegative6674 p) (nonnegative6669 p)
def d6676 (p : Pattern) : Int := if p 204 then d12 p else d6594 p
theorem agree6676 (p q : Pattern) (h : Agree support p q) : d6676 p = d6676 q := by
  simp only [d6676, h 204 (by decide), agree12 p q h, agree6594 p q h]
theorem nonnegative6676 (p : Pattern) : 0 ≤ d6676 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6594 p)
def d6677 (p : Pattern) : Int := if p 182 then d6676 p else d6595 p
theorem agree6677 (p q : Pattern) (h : Agree support p q) : d6677 p = d6677 q := by
  simp only [d6677, h 182 (by decide), agree6676 p q h, agree6595 p q h]
theorem nonnegative6677 (p : Pattern) : 0 ≤ d6677 p :=
  nonnegative_ite (p 182) (nonnegative6676 p) (nonnegative6595 p)
def d6678 (p : Pattern) : Int := if p 204 then d12 p else d6618 p
theorem agree6678 (p q : Pattern) (h : Agree support p q) : d6678 p = d6678 q := by
  simp only [d6678, h 204 (by decide), agree12 p q h, agree6618 p q h]
theorem nonnegative6678 (p : Pattern) : 0 ≤ d6678 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6618 p)
def d6679 (p : Pattern) : Int := if p 182 then d6678 p else d6619 p
theorem agree6679 (p q : Pattern) (h : Agree support p q) : d6679 p = d6679 q := by
  simp only [d6679, h 182 (by decide), agree6678 p q h, agree6619 p q h]
theorem nonnegative6679 (p : Pattern) : 0 ≤ d6679 p :=
  nonnegative_ite (p 182) (nonnegative6678 p) (nonnegative6619 p)
def d6680 (p : Pattern) : Int := if p 163 then d6679 p else d6677 p
theorem agree6680 (p q : Pattern) (h : Agree support p q) : d6680 p = d6680 q := by
  simp only [d6680, h 163 (by decide), agree6679 p q h, agree6677 p q h]
theorem nonnegative6680 (p : Pattern) : 0 ≤ d6680 p :=
  nonnegative_ite (p 163) (nonnegative6679 p) (nonnegative6677 p)
def d6681 (p : Pattern) : Int := if p 162 then d6680 p else d6675 p
theorem agree6681 (p q : Pattern) (h : Agree support p q) : d6681 p = d6681 q := by
  simp only [d6681, h 162 (by decide), agree6680 p q h, agree6675 p q h]
theorem nonnegative6681 (p : Pattern) : 0 ≤ d6681 p :=
  nonnegative_ite (p 162) (nonnegative6680 p) (nonnegative6675 p)
def d6682 (p : Pattern) : Int := if p 204 then d12 p else d6580 p
theorem agree6682 (p q : Pattern) (h : Agree support p q) : d6682 p = d6682 q := by
  simp only [d6682, h 204 (by decide), agree12 p q h, agree6580 p q h]
theorem nonnegative6682 (p : Pattern) : 0 ≤ d6682 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6580 p)
def d6683 (p : Pattern) : Int := if p 182 then d6682 p else d6581 p
theorem agree6683 (p q : Pattern) (h : Agree support p q) : d6683 p = d6683 q := by
  simp only [d6683, h 182 (by decide), agree6682 p q h, agree6581 p q h]
theorem nonnegative6683 (p : Pattern) : 0 ≤ d6683 p :=
  nonnegative_ite (p 182) (nonnegative6682 p) (nonnegative6581 p)
def d6684 (p : Pattern) : Int := if p 163 then d12 p else d6683 p
theorem agree6684 (p q : Pattern) (h : Agree support p q) : d6684 p = d6684 q := by
  simp only [d6684, h 163 (by decide), agree12 p q h, agree6683 p q h]
theorem nonnegative6684 (p : Pattern) : 0 ≤ d6684 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6683 p)
def d6685 (p : Pattern) : Int := if p 162 then d6684 p else d6680 p
theorem agree6685 (p q : Pattern) (h : Agree support p q) : d6685 p = d6685 q := by
  simp only [d6685, h 162 (by decide), agree6684 p q h, agree6680 p q h]
theorem nonnegative6685 (p : Pattern) : 0 ≤ d6685 p :=
  nonnegative_ite (p 162) (nonnegative6684 p) (nonnegative6680 p)
def d6686 (p : Pattern) : Int := if p 161 then d6685 p else d6681 p
theorem agree6686 (p q : Pattern) (h : Agree support p q) : d6686 p = d6686 q := by
  simp only [d6686, h 161 (by decide), agree6685 p q h, agree6681 p q h]
theorem nonnegative6686 (p : Pattern) : 0 ≤ d6686 p :=
  nonnegative_ite (p 161) (nonnegative6685 p) (nonnegative6681 p)
def d6687 (p : Pattern) : Int := if p 182 then d6602 p else d6652 p
theorem agree6687 (p q : Pattern) (h : Agree support p q) : d6687 p = d6687 q := by
  simp only [d6687, h 182 (by decide), agree6602 p q h, agree6652 p q h]
theorem nonnegative6687 (p : Pattern) : 0 ≤ d6687 p :=
  nonnegative_ite (p 182) (nonnegative6602 p) (nonnegative6652 p)
def d6688 (p : Pattern) : Int := if p 204 then d6607 p else d6 p
theorem agree6688 (p q : Pattern) (h : Agree support p q) : d6688 p = d6688 q := by
  simp only [d6688, h 204 (by decide), agree6607 p q h, agree6 p q h]
theorem nonnegative6688 (p : Pattern) : 0 ≤ d6688 p :=
  nonnegative_ite (p 204) (nonnegative6607 p) (nonnegative6 p)
def d6689 (p : Pattern) : Int := if p 182 then d6608 p else d6688 p
theorem agree6689 (p q : Pattern) (h : Agree support p q) : d6689 p = d6689 q := by
  simp only [d6689, h 182 (by decide), agree6608 p q h, agree6688 p q h]
theorem nonnegative6689 (p : Pattern) : 0 ≤ d6689 p :=
  nonnegative_ite (p 182) (nonnegative6608 p) (nonnegative6688 p)
def d6690 (p : Pattern) : Int := if p 163 then d6689 p else d6687 p
theorem agree6690 (p q : Pattern) (h : Agree support p q) : d6690 p = d6690 q := by
  simp only [d6690, h 163 (by decide), agree6689 p q h, agree6687 p q h]
theorem nonnegative6690 (p : Pattern) : 0 ≤ d6690 p :=
  nonnegative_ite (p 163) (nonnegative6689 p) (nonnegative6687 p)
def d6691 (p : Pattern) : Int := if p 162 then d6649 p else d6690 p
theorem agree6691 (p q : Pattern) (h : Agree support p q) : d6691 p = d6691 q := by
  simp only [d6691, h 162 (by decide), agree6649 p q h, agree6690 p q h]
theorem nonnegative6691 (p : Pattern) : 0 ≤ d6691 p :=
  nonnegative_ite (p 162) (nonnegative6649 p) (nonnegative6690 p)
def d6692 (p : Pattern) : Int := if p 161 then d12 p else d6691 p
theorem agree6692 (p q : Pattern) (h : Agree support p q) : d6692 p = d6692 q := by
  simp only [d6692, h 161 (by decide), agree12 p q h, agree6691 p q h]
theorem nonnegative6692 (p : Pattern) : 0 ≤ d6692 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6691 p)
def d6693 (p : Pattern) : Int := if p 160 then d6692 p else d6686 p
theorem agree6693 (p q : Pattern) (h : Agree support p q) : d6693 p = d6693 q := by
  simp only [d6693, h 160 (by decide), agree6692 p q h, agree6686 p q h]
theorem nonnegative6693 (p : Pattern) : 0 ≤ d6693 p :=
  nonnegative_ite (p 160) (nonnegative6692 p) (nonnegative6686 p)
def d6694 (p : Pattern) : Int := if p 163 then d6687 p else d6674 p
theorem agree6694 (p q : Pattern) (h : Agree support p q) : d6694 p = d6694 q := by
  simp only [d6694, h 163 (by decide), agree6687 p q h, agree6674 p q h]
theorem nonnegative6694 (p : Pattern) : 0 ≤ d6694 p :=
  nonnegative_ite (p 163) (nonnegative6687 p) (nonnegative6674 p)
def d6695 (p : Pattern) : Int := if p 163 then d6683 p else d6679 p
theorem agree6695 (p q : Pattern) (h : Agree support p q) : d6695 p = d6695 q := by
  simp only [d6695, h 163 (by decide), agree6683 p q h, agree6679 p q h]
theorem nonnegative6695 (p : Pattern) : 0 ≤ d6695 p :=
  nonnegative_ite (p 163) (nonnegative6683 p) (nonnegative6679 p)
def d6696 (p : Pattern) : Int := if p 162 then d6695 p else d6694 p
theorem agree6696 (p q : Pattern) (h : Agree support p q) : d6696 p = d6696 q := by
  simp only [d6696, h 162 (by decide), agree6695 p q h, agree6694 p q h]
theorem nonnegative6696 (p : Pattern) : 0 ≤ d6696 p :=
  nonnegative_ite (p 162) (nonnegative6695 p) (nonnegative6694 p)
def d6697 (p : Pattern) : Int := if p 163 then d6645 p else d6679 p
theorem agree6697 (p q : Pattern) (h : Agree support p q) : d6697 p = d6697 q := by
  simp only [d6697, h 163 (by decide), agree6645 p q h, agree6679 p q h]
theorem nonnegative6697 (p : Pattern) : 0 ≤ d6697 p :=
  nonnegative_ite (p 163) (nonnegative6645 p) (nonnegative6679 p)
def d6698 (p : Pattern) : Int := if p 162 then d6649 p else d6697 p
theorem agree6698 (p q : Pattern) (h : Agree support p q) : d6698 p = d6698 q := by
  simp only [d6698, h 162 (by decide), agree6649 p q h, agree6697 p q h]
theorem nonnegative6698 (p : Pattern) : 0 ≤ d6698 p :=
  nonnegative_ite (p 162) (nonnegative6649 p) (nonnegative6697 p)
def d6699 (p : Pattern) : Int := if p 161 then d6698 p else d6696 p
theorem agree6699 (p q : Pattern) (h : Agree support p q) : d6699 p = d6699 q := by
  simp only [d6699, h 161 (by decide), agree6698 p q h, agree6696 p q h]
theorem nonnegative6699 (p : Pattern) : 0 ≤ d6699 p :=
  nonnegative_ite (p 161) (nonnegative6698 p) (nonnegative6696 p)
def d6700 (p : Pattern) : Int := if p 163 then d12 p else d6689 p
theorem agree6700 (p q : Pattern) (h : Agree support p q) : d6700 p = d6700 q := by
  simp only [d6700, h 163 (by decide), agree12 p q h, agree6689 p q h]
theorem nonnegative6700 (p : Pattern) : 0 ≤ d6700 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6689 p)
def d6701 (p : Pattern) : Int := if p 162 then d12 p else d6700 p
theorem agree6701 (p q : Pattern) (h : Agree support p q) : d6701 p = d6701 q := by
  simp only [d6701, h 162 (by decide), agree12 p q h, agree6700 p q h]
theorem nonnegative6701 (p : Pattern) : 0 ≤ d6701 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6700 p)
def d6702 (p : Pattern) : Int := if p 161 then d12 p else d6701 p
theorem agree6702 (p q : Pattern) (h : Agree support p q) : d6702 p = d6702 q := by
  simp only [d6702, h 161 (by decide), agree12 p q h, agree6701 p q h]
theorem nonnegative6702 (p : Pattern) : 0 ≤ d6702 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6701 p)
def d6703 (p : Pattern) : Int := if p 160 then d6702 p else d6699 p
theorem agree6703 (p q : Pattern) (h : Agree support p q) : d6703 p = d6703 q := by
  simp only [d6703, h 160 (by decide), agree6702 p q h, agree6699 p q h]
theorem nonnegative6703 (p : Pattern) : 0 ≤ d6703 p :=
  nonnegative_ite (p 160) (nonnegative6702 p) (nonnegative6699 p)
def d6704 (p : Pattern) : Int := if p 141 then d6703 p else d6693 p
theorem agree6704 (p q : Pattern) (h : Agree support p q) : d6704 p = d6704 q := by
  simp only [d6704, h 141 (by decide), agree6703 p q h, agree6693 p q h]
theorem nonnegative6704 (p : Pattern) : 0 ≤ d6704 p :=
  nonnegative_ite (p 141) (nonnegative6703 p) (nonnegative6693 p)
def d6705 (p : Pattern) : Int := if p 138 then d6704 p else d6664 p
theorem agree6705 (p q : Pattern) (h : Agree support p q) : d6705 p = d6705 q := by
  simp only [d6705, h 138 (by decide), agree6704 p q h, agree6664 p q h]
theorem nonnegative6705 (p : Pattern) : 0 ≤ d6705 p :=
  nonnegative_ite (p 138) (nonnegative6704 p) (nonnegative6664 p)
def d6706 (p : Pattern) : Int := if p 163 then d6648 p else d6683 p
theorem agree6706 (p q : Pattern) (h : Agree support p q) : d6706 p = d6706 q := by
  simp only [d6706, h 163 (by decide), agree6648 p q h, agree6683 p q h]
theorem nonnegative6706 (p : Pattern) : 0 ≤ d6706 p :=
  nonnegative_ite (p 163) (nonnegative6648 p) (nonnegative6683 p)
def d6707 (p : Pattern) : Int := if p 162 then d6649 p else d6706 p
theorem agree6707 (p q : Pattern) (h : Agree support p q) : d6707 p = d6707 q := by
  simp only [d6707, h 162 (by decide), agree6649 p q h, agree6706 p q h]
theorem nonnegative6707 (p : Pattern) : 0 ≤ d6707 p :=
  nonnegative_ite (p 162) (nonnegative6649 p) (nonnegative6706 p)
def d6708 (p : Pattern) : Int := if p 162 then d12 p else d6649 p
theorem agree6708 (p q : Pattern) (h : Agree support p q) : d6708 p = d6708 q := by
  simp only [d6708, h 162 (by decide), agree12 p q h, agree6649 p q h]
theorem nonnegative6708 (p : Pattern) : 0 ≤ d6708 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6649 p)
def d6709 (p : Pattern) : Int := if p 161 then d6708 p else d6707 p
theorem agree6709 (p q : Pattern) (h : Agree support p q) : d6709 p = d6709 q := by
  simp only [d6709, h 161 (by decide), agree6708 p q h, agree6707 p q h]
theorem nonnegative6709 (p : Pattern) : 0 ≤ d6709 p :=
  nonnegative_ite (p 161) (nonnegative6708 p) (nonnegative6707 p)
def d6710 (p : Pattern) : Int := if p 161 then d12 p else d6708 p
theorem agree6710 (p q : Pattern) (h : Agree support p q) : d6710 p = d6710 q := by
  simp only [d6710, h 161 (by decide), agree12 p q h, agree6708 p q h]
theorem nonnegative6710 (p : Pattern) : 0 ≤ d6710 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6708 p)
def d6711 (p : Pattern) : Int := if p 160 then d6710 p else d6709 p
theorem agree6711 (p q : Pattern) (h : Agree support p q) : d6711 p = d6711 q := by
  simp only [d6711, h 160 (by decide), agree6710 p q h, agree6709 p q h]
theorem nonnegative6711 (p : Pattern) : 0 ≤ d6711 p :=
  nonnegative_ite (p 160) (nonnegative6710 p) (nonnegative6709 p)
def d6712 (p : Pattern) : Int := if p 160 then d12 p else d6710 p
theorem agree6712 (p q : Pattern) (h : Agree support p q) : d6712 p = d6712 q := by
  simp only [d6712, h 160 (by decide), agree12 p q h, agree6710 p q h]
theorem nonnegative6712 (p : Pattern) : 0 ≤ d6712 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative6710 p)
def d6713 (p : Pattern) : Int := if p 141 then d6712 p else d6711 p
theorem agree6713 (p q : Pattern) (h : Agree support p q) : d6713 p = d6713 q := by
  simp only [d6713, h 141 (by decide), agree6712 p q h, agree6711 p q h]
theorem nonnegative6713 (p : Pattern) : 0 ≤ d6713 p :=
  nonnegative_ite (p 141) (nonnegative6712 p) (nonnegative6711 p)
def d6714 (p : Pattern) : Int := if p 138 then d6713 p else d6704 p
theorem agree6714 (p q : Pattern) (h : Agree support p q) : d6714 p = d6714 q := by
  simp only [d6714, h 138 (by decide), agree6713 p q h, agree6704 p q h]
theorem nonnegative6714 (p : Pattern) : 0 ≤ d6714 p :=
  nonnegative_ite (p 138) (nonnegative6713 p) (nonnegative6704 p)
def d6715 (p : Pattern) : Int := if p 116 then d6714 p else d6705 p
theorem agree6715 (p q : Pattern) (h : Agree support p q) : d6715 p = d6715 q := by
  simp only [d6715, h 116 (by decide), agree6714 p q h, agree6705 p q h]
theorem nonnegative6715 (p : Pattern) : 0 ≤ d6715 p :=
  nonnegative_ite (p 116) (nonnegative6714 p) (nonnegative6705 p)
def d6716 (p : Pattern) : Int := if p 138 then d12 p else d6704 p
theorem agree6716 (p q : Pattern) (h : Agree support p q) : d6716 p = d6716 q := by
  simp only [d6716, h 138 (by decide), agree12 p q h, agree6704 p q h]
theorem nonnegative6716 (p : Pattern) : 0 ≤ d6716 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6704 p)
def d6717 (p : Pattern) : Int := if p 116 then d6716 p else d6705 p
theorem agree6717 (p q : Pattern) (h : Agree support p q) : d6717 p = d6717 q := by
  simp only [d6717, h 116 (by decide), agree6716 p q h, agree6705 p q h]
theorem nonnegative6717 (p : Pattern) : 0 ≤ d6717 p :=
  nonnegative_ite (p 116) (nonnegative6716 p) (nonnegative6705 p)
def d6718 (p : Pattern) : Int := if p 115 then d6717 p else d6715 p
theorem agree6718 (p q : Pattern) (h : Agree support p q) : d6718 p = d6718 q := by
  simp only [d6718, h 115 (by decide), agree6717 p q h, agree6715 p q h]
theorem nonnegative6718 (p : Pattern) : 0 ≤ d6718 p :=
  nonnegative_ite (p 115) (nonnegative6717 p) (nonnegative6715 p)
def d6719 (p : Pattern) : Int := if p 246 then d5 p else d1 p
theorem agree6719 (p q : Pattern) (h : Agree support p q) : d6719 p = d6719 q := by
  simp only [d6719, h 246 (by decide), agree5 p q h, agree1 p q h]
theorem nonnegative6719 (p : Pattern) : 0 ≤ d6719 p :=
  nonnegative_ite (p 246) (nonnegative5 p) (nonnegative1 p)
end NetHack.Sokoban22Refined85
