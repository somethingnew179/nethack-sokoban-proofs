/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes55
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6720 (p : Pattern) : Int := if p 225 then d6719 p else d1 p
theorem agree6720 (p q : Pattern) (h : Agree support p q) : d6720 p = d6720 q := by
  simp only [d6720, h 225 (by decide), agree6719 p q h, agree1 p q h]
theorem nonnegative6720 (p : Pattern) : 0 ≤ d6720 p :=
  nonnegative_ite (p 225) (nonnegative6719 p) (nonnegative1 p)
def d6721 (p : Pattern) : Int := if p 224 then d6719 p else d6720 p
theorem agree6721 (p q : Pattern) (h : Agree support p q) : d6721 p = d6721 q := by
  simp only [d6721, h 224 (by decide), agree6719 p q h, agree6720 p q h]
theorem nonnegative6721 (p : Pattern) : 0 ≤ d6721 p :=
  nonnegative_ite (p 224) (nonnegative6719 p) (nonnegative6720 p)
def d6722 (p : Pattern) : Int := if p 204 then d6721 p else d1 p
theorem agree6722 (p q : Pattern) (h : Agree support p q) : d6722 p = d6722 q := by
  simp only [d6722, h 204 (by decide), agree6721 p q h, agree1 p q h]
theorem nonnegative6722 (p : Pattern) : 0 ≤ d6722 p :=
  nonnegative_ite (p 204) (nonnegative6721 p) (nonnegative1 p)
def d6723 (p : Pattern) : Int := if p 246 then d3 p else d1 p
theorem agree6723 (p q : Pattern) (h : Agree support p q) : d6723 p = d6723 q := by
  simp only [d6723, h 246 (by decide), agree3 p q h, agree1 p q h]
theorem nonnegative6723 (p : Pattern) : 0 ≤ d6723 p :=
  nonnegative_ite (p 246) (nonnegative3 p) (nonnegative1 p)
def d6724 (p : Pattern) : Int := if p 225 then d6723 p else d1 p
theorem agree6724 (p q : Pattern) (h : Agree support p q) : d6724 p = d6724 q := by
  simp only [d6724, h 225 (by decide), agree6723 p q h, agree1 p q h]
theorem nonnegative6724 (p : Pattern) : 0 ≤ d6724 p :=
  nonnegative_ite (p 225) (nonnegative6723 p) (nonnegative1 p)
def d6725 (p : Pattern) : Int := if p 224 then d6723 p else d6724 p
theorem agree6725 (p q : Pattern) (h : Agree support p q) : d6725 p = d6725 q := by
  simp only [d6725, h 224 (by decide), agree6723 p q h, agree6724 p q h]
theorem nonnegative6725 (p : Pattern) : 0 ≤ d6725 p :=
  nonnegative_ite (p 224) (nonnegative6723 p) (nonnegative6724 p)
def d6726 (p : Pattern) : Int := if p 204 then d12 p else d6725 p
theorem agree6726 (p q : Pattern) (h : Agree support p q) : d6726 p = d6726 q := by
  simp only [d6726, h 204 (by decide), agree12 p q h, agree6725 p q h]
theorem nonnegative6726 (p : Pattern) : 0 ≤ d6726 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6725 p)
def d6727 (p : Pattern) : Int := if p 182 then d6726 p else d6722 p
theorem agree6727 (p q : Pattern) (h : Agree support p q) : d6727 p = d6727 q := by
  simp only [d6727, h 182 (by decide), agree6726 p q h, agree6722 p q h]
theorem nonnegative6727 (p : Pattern) : 0 ≤ d6727 p :=
  nonnegative_ite (p 182) (nonnegative6726 p) (nonnegative6722 p)
def d6728 (p : Pattern) : Int := if p 246 then d9 p else d5 p
theorem agree6728 (p q : Pattern) (h : Agree support p q) : d6728 p = d6728 q := by
  simp only [d6728, h 246 (by decide), agree9 p q h, agree5 p q h]
theorem nonnegative6728 (p : Pattern) : 0 ≤ d6728 p :=
  nonnegative_ite (p 246) (nonnegative9 p) (nonnegative5 p)
def d6729 (p : Pattern) : Int := if p 225 then d6728 p else d5 p
theorem agree6729 (p q : Pattern) (h : Agree support p q) : d6729 p = d6729 q := by
  simp only [d6729, h 225 (by decide), agree6728 p q h, agree5 p q h]
theorem nonnegative6729 (p : Pattern) : 0 ≤ d6729 p :=
  nonnegative_ite (p 225) (nonnegative6728 p) (nonnegative5 p)
def d6730 (p : Pattern) : Int := if p 224 then d6728 p else d6729 p
theorem agree6730 (p q : Pattern) (h : Agree support p q) : d6730 p = d6730 q := by
  simp only [d6730, h 224 (by decide), agree6728 p q h, agree6729 p q h]
theorem nonnegative6730 (p : Pattern) : 0 ≤ d6730 p :=
  nonnegative_ite (p 224) (nonnegative6728 p) (nonnegative6729 p)
def d6731 (p : Pattern) : Int := if p 204 then d6730 p else d5 p
theorem agree6731 (p q : Pattern) (h : Agree support p q) : d6731 p = d6731 q := by
  simp only [d6731, h 204 (by decide), agree6730 p q h, agree5 p q h]
theorem nonnegative6731 (p : Pattern) : 0 ≤ d6731 p :=
  nonnegative_ite (p 204) (nonnegative6730 p) (nonnegative5 p)
def d6732 (p : Pattern) : Int := if p 246 then d7 p else d5 p
theorem agree6732 (p q : Pattern) (h : Agree support p q) : d6732 p = d6732 q := by
  simp only [d6732, h 246 (by decide), agree7 p q h, agree5 p q h]
theorem nonnegative6732 (p : Pattern) : 0 ≤ d6732 p :=
  nonnegative_ite (p 246) (nonnegative7 p) (nonnegative5 p)
def d6733 (p : Pattern) : Int := if p 225 then d6732 p else d5 p
theorem agree6733 (p q : Pattern) (h : Agree support p q) : d6733 p = d6733 q := by
  simp only [d6733, h 225 (by decide), agree6732 p q h, agree5 p q h]
theorem nonnegative6733 (p : Pattern) : 0 ≤ d6733 p :=
  nonnegative_ite (p 225) (nonnegative6732 p) (nonnegative5 p)
def d6734 (p : Pattern) : Int := if p 224 then d6732 p else d6733 p
theorem agree6734 (p q : Pattern) (h : Agree support p q) : d6734 p = d6734 q := by
  simp only [d6734, h 224 (by decide), agree6732 p q h, agree6733 p q h]
theorem nonnegative6734 (p : Pattern) : 0 ≤ d6734 p :=
  nonnegative_ite (p 224) (nonnegative6732 p) (nonnegative6733 p)
def d6735 (p : Pattern) : Int := if p 204 then d12 p else d6734 p
theorem agree6735 (p q : Pattern) (h : Agree support p q) : d6735 p = d6735 q := by
  simp only [d6735, h 204 (by decide), agree12 p q h, agree6734 p q h]
theorem nonnegative6735 (p : Pattern) : 0 ≤ d6735 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6734 p)
def d6736 (p : Pattern) : Int := if p 182 then d6735 p else d6731 p
theorem agree6736 (p q : Pattern) (h : Agree support p q) : d6736 p = d6736 q := by
  simp only [d6736, h 182 (by decide), agree6735 p q h, agree6731 p q h]
theorem nonnegative6736 (p : Pattern) : 0 ≤ d6736 p :=
  nonnegative_ite (p 182) (nonnegative6735 p) (nonnegative6731 p)
def d6737 (p : Pattern) : Int := if p 163 then d6736 p else d6727 p
theorem agree6737 (p q : Pattern) (h : Agree support p q) : d6737 p = d6737 q := by
  simp only [d6737, h 163 (by decide), agree6736 p q h, agree6727 p q h]
theorem nonnegative6737 (p : Pattern) : 0 ≤ d6737 p :=
  nonnegative_ite (p 163) (nonnegative6736 p) (nonnegative6727 p)
def d6738 (p : Pattern) : Int := if p 162 then d6737 p else d6727 p
theorem agree6738 (p q : Pattern) (h : Agree support p q) : d6738 p = d6738 q := by
  simp only [d6738, h 162 (by decide), agree6737 p q h, agree6727 p q h]
theorem nonnegative6738 (p : Pattern) : 0 ≤ d6738 p :=
  nonnegative_ite (p 162) (nonnegative6737 p) (nonnegative6727 p)
def d6739 (p : Pattern) : Int := if p 163 then d12 p else d6645 p
theorem agree6739 (p q : Pattern) (h : Agree support p q) : d6739 p = d6739 q := by
  simp only [d6739, h 163 (by decide), agree12 p q h, agree6645 p q h]
theorem nonnegative6739 (p : Pattern) : 0 ≤ d6739 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6645 p)
def d6740 (p : Pattern) : Int := if p 162 then d6739 p else d6737 p
theorem agree6740 (p q : Pattern) (h : Agree support p q) : d6740 p = d6740 q := by
  simp only [d6740, h 162 (by decide), agree6739 p q h, agree6737 p q h]
theorem nonnegative6740 (p : Pattern) : 0 ≤ d6740 p :=
  nonnegative_ite (p 162) (nonnegative6739 p) (nonnegative6737 p)
def d6741 (p : Pattern) : Int := if p 161 then d6740 p else d6738 p
theorem agree6741 (p q : Pattern) (h : Agree support p q) : d6741 p = d6741 q := by
  simp only [d6741, h 161 (by decide), agree6740 p q h, agree6738 p q h]
theorem nonnegative6741 (p : Pattern) : 0 ≤ d6741 p :=
  nonnegative_ite (p 161) (nonnegative6740 p) (nonnegative6738 p)
def d6742 (p : Pattern) : Int := if p 246 then d7 p else d1 p
theorem agree6742 (p q : Pattern) (h : Agree support p q) : d6742 p = d6742 q := by
  simp only [d6742, h 246 (by decide), agree7 p q h, agree1 p q h]
theorem nonnegative6742 (p : Pattern) : 0 ≤ d6742 p :=
  nonnegative_ite (p 246) (nonnegative7 p) (nonnegative1 p)
def d6743 (p : Pattern) : Int := if p 225 then d6742 p else d1 p
theorem agree6743 (p q : Pattern) (h : Agree support p q) : d6743 p = d6743 q := by
  simp only [d6743, h 225 (by decide), agree6742 p q h, agree1 p q h]
theorem nonnegative6743 (p : Pattern) : 0 ≤ d6743 p :=
  nonnegative_ite (p 225) (nonnegative6742 p) (nonnegative1 p)
def d6744 (p : Pattern) : Int := if p 246 then d10 p else d1 p
theorem agree6744 (p q : Pattern) (h : Agree support p q) : d6744 p = d6744 q := by
  simp only [d6744, h 246 (by decide), agree10 p q h, agree1 p q h]
theorem nonnegative6744 (p : Pattern) : 0 ≤ d6744 p :=
  nonnegative_ite (p 246) (nonnegative10 p) (nonnegative1 p)
def d6745 (p : Pattern) : Int := if p 225 then d6744 p else d6719 p
theorem agree6745 (p q : Pattern) (h : Agree support p q) : d6745 p = d6745 q := by
  simp only [d6745, h 225 (by decide), agree6744 p q h, agree6719 p q h]
theorem nonnegative6745 (p : Pattern) : 0 ≤ d6745 p :=
  nonnegative_ite (p 225) (nonnegative6744 p) (nonnegative6719 p)
def d6746 (p : Pattern) : Int := if p 224 then d6745 p else d6743 p
theorem agree6746 (p q : Pattern) (h : Agree support p q) : d6746 p = d6746 q := by
  simp only [d6746, h 224 (by decide), agree6745 p q h, agree6743 p q h]
theorem nonnegative6746 (p : Pattern) : 0 ≤ d6746 p :=
  nonnegative_ite (p 224) (nonnegative6745 p) (nonnegative6743 p)
def d6747 (p : Pattern) : Int := if p 204 then d6746 p else d1 p
theorem agree6747 (p q : Pattern) (h : Agree support p q) : d6747 p = d6747 q := by
  simp only [d6747, h 204 (by decide), agree6746 p q h, agree1 p q h]
theorem nonnegative6747 (p : Pattern) : 0 ≤ d6747 p :=
  nonnegative_ite (p 204) (nonnegative6746 p) (nonnegative1 p)
def d6748 (p : Pattern) : Int := if p 246 then d9 p else d3 p
theorem agree6748 (p q : Pattern) (h : Agree support p q) : d6748 p = d6748 q := by
  simp only [d6748, h 246 (by decide), agree9 p q h, agree3 p q h]
theorem nonnegative6748 (p : Pattern) : 0 ≤ d6748 p :=
  nonnegative_ite (p 246) (nonnegative9 p) (nonnegative3 p)
def d6749 (p : Pattern) : Int := if p 225 then d6748 p else d3 p
theorem agree6749 (p q : Pattern) (h : Agree support p q) : d6749 p = d6749 q := by
  simp only [d6749, h 225 (by decide), agree6748 p q h, agree3 p q h]
theorem nonnegative6749 (p : Pattern) : 0 ≤ d6749 p :=
  nonnegative_ite (p 225) (nonnegative6748 p) (nonnegative3 p)
def d6750 (p : Pattern) : Int := if p 246 then d7 p else d3 p
theorem agree6750 (p q : Pattern) (h : Agree support p q) : d6750 p = d6750 q := by
  simp only [d6750, h 246 (by decide), agree7 p q h, agree3 p q h]
theorem nonnegative6750 (p : Pattern) : 0 ≤ d6750 p :=
  nonnegative_ite (p 246) (nonnegative7 p) (nonnegative3 p)
def d6751 (p : Pattern) : Int := if p 225 then d3374 p else d6750 p
theorem agree6751 (p q : Pattern) (h : Agree support p q) : d6751 p = d6751 q := by
  simp only [d6751, h 225 (by decide), agree3374 p q h, agree6750 p q h]
theorem nonnegative6751 (p : Pattern) : 0 ≤ d6751 p :=
  nonnegative_ite (p 225) (nonnegative3374 p) (nonnegative6750 p)
def d6752 (p : Pattern) : Int := if p 224 then d6751 p else d6749 p
theorem agree6752 (p q : Pattern) (h : Agree support p q) : d6752 p = d6752 q := by
  simp only [d6752, h 224 (by decide), agree6751 p q h, agree6749 p q h]
theorem nonnegative6752 (p : Pattern) : 0 ≤ d6752 p :=
  nonnegative_ite (p 224) (nonnegative6751 p) (nonnegative6749 p)
def d6753 (p : Pattern) : Int := if p 204 then d12 p else d6752 p
theorem agree6753 (p q : Pattern) (h : Agree support p q) : d6753 p = d6753 q := by
  simp only [d6753, h 204 (by decide), agree12 p q h, agree6752 p q h]
theorem nonnegative6753 (p : Pattern) : 0 ≤ d6753 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6752 p)
def d6754 (p : Pattern) : Int := if p 182 then d6753 p else d6747 p
theorem agree6754 (p q : Pattern) (h : Agree support p q) : d6754 p = d6754 q := by
  simp only [d6754, h 182 (by decide), agree6753 p q h, agree6747 p q h]
theorem nonnegative6754 (p : Pattern) : 0 ≤ d6754 p :=
  nonnegative_ite (p 182) (nonnegative6753 p) (nonnegative6747 p)
def d6755 (p : Pattern) : Int := if p 225 then d3377 p else d7 p
theorem agree6755 (p q : Pattern) (h : Agree support p q) : d6755 p = d6755 q := by
  simp only [d6755, h 225 (by decide), agree3377 p q h, agree7 p q h]
theorem nonnegative6755 (p : Pattern) : 0 ≤ d6755 p :=
  nonnegative_ite (p 225) (nonnegative3377 p) (nonnegative7 p)
def d6756 (p : Pattern) : Int := if p 246 then d11 p else d7 p
theorem agree6756 (p q : Pattern) (h : Agree support p q) : d6756 p = d6756 q := by
  simp only [d6756, h 246 (by decide), agree11 p q h, agree7 p q h]
theorem nonnegative6756 (p : Pattern) : 0 ≤ d6756 p :=
  nonnegative_ite (p 246) (nonnegative11 p) (nonnegative7 p)
def d6757 (p : Pattern) : Int := if p 225 then d3377 p else d6756 p
theorem agree6757 (p q : Pattern) (h : Agree support p q) : d6757 p = d6757 q := by
  simp only [d6757, h 225 (by decide), agree3377 p q h, agree6756 p q h]
theorem nonnegative6757 (p : Pattern) : 0 ≤ d6757 p :=
  nonnegative_ite (p 225) (nonnegative3377 p) (nonnegative6756 p)
def d6758 (p : Pattern) : Int := if p 224 then d6757 p else d6755 p
theorem agree6758 (p q : Pattern) (h : Agree support p q) : d6758 p = d6758 q := by
  simp only [d6758, h 224 (by decide), agree6757 p q h, agree6755 p q h]
theorem nonnegative6758 (p : Pattern) : 0 ≤ d6758 p :=
  nonnegative_ite (p 224) (nonnegative6757 p) (nonnegative6755 p)
def d6759 (p : Pattern) : Int := if p 204 then d12 p else d6758 p
theorem agree6759 (p q : Pattern) (h : Agree support p q) : d6759 p = d6759 q := by
  simp only [d6759, h 204 (by decide), agree12 p q h, agree6758 p q h]
theorem nonnegative6759 (p : Pattern) : 0 ≤ d6759 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6758 p)
def d6760 (p : Pattern) : Int := if p 182 then d6759 p else d6747 p
theorem agree6760 (p q : Pattern) (h : Agree support p q) : d6760 p = d6760 q := by
  simp only [d6760, h 182 (by decide), agree6759 p q h, agree6747 p q h]
theorem nonnegative6760 (p : Pattern) : 0 ≤ d6760 p :=
  nonnegative_ite (p 182) (nonnegative6759 p) (nonnegative6747 p)
def d6761 (p : Pattern) : Int := if p 163 then d6760 p else d6754 p
theorem agree6761 (p q : Pattern) (h : Agree support p q) : d6761 p = d6761 q := by
  simp only [d6761, h 163 (by decide), agree6760 p q h, agree6754 p q h]
theorem nonnegative6761 (p : Pattern) : 0 ≤ d6761 p :=
  nonnegative_ite (p 163) (nonnegative6760 p) (nonnegative6754 p)
def d6762 (p : Pattern) : Int := if p 182 then d12 p else d6747 p
theorem agree6762 (p q : Pattern) (h : Agree support p q) : d6762 p = d6762 q := by
  simp only [d6762, h 182 (by decide), agree12 p q h, agree6747 p q h]
theorem nonnegative6762 (p : Pattern) : 0 ≤ d6762 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6747 p)
def d6763 (p : Pattern) : Int := if p 246 then d11 p else d5 p
theorem agree6763 (p q : Pattern) (h : Agree support p q) : d6763 p = d6763 q := by
  simp only [d6763, h 246 (by decide), agree11 p q h, agree5 p q h]
theorem nonnegative6763 (p : Pattern) : 0 ≤ d6763 p :=
  nonnegative_ite (p 246) (nonnegative11 p) (nonnegative5 p)
def d6764 (p : Pattern) : Int := if p 225 then d6763 p else d5 p
theorem agree6764 (p q : Pattern) (h : Agree support p q) : d6764 p = d6764 q := by
  simp only [d6764, h 225 (by decide), agree6763 p q h, agree5 p q h]
theorem nonnegative6764 (p : Pattern) : 0 ≤ d6764 p :=
  nonnegative_ite (p 225) (nonnegative6763 p) (nonnegative5 p)
def d6765 (p : Pattern) : Int := if p 225 then d3366 p else d6728 p
theorem agree6765 (p q : Pattern) (h : Agree support p q) : d6765 p = d6765 q := by
  simp only [d6765, h 225 (by decide), agree3366 p q h, agree6728 p q h]
theorem nonnegative6765 (p : Pattern) : 0 ≤ d6765 p :=
  nonnegative_ite (p 225) (nonnegative3366 p) (nonnegative6728 p)
def d6766 (p : Pattern) : Int := if p 224 then d6765 p else d6764 p
theorem agree6766 (p q : Pattern) (h : Agree support p q) : d6766 p = d6766 q := by
  simp only [d6766, h 224 (by decide), agree6765 p q h, agree6764 p q h]
theorem nonnegative6766 (p : Pattern) : 0 ≤ d6766 p :=
  nonnegative_ite (p 224) (nonnegative6765 p) (nonnegative6764 p)
def d6767 (p : Pattern) : Int := if p 204 then d6766 p else d5 p
theorem agree6767 (p q : Pattern) (h : Agree support p q) : d6767 p = d6767 q := by
  simp only [d6767, h 204 (by decide), agree6766 p q h, agree5 p q h]
theorem nonnegative6767 (p : Pattern) : 0 ≤ d6767 p :=
  nonnegative_ite (p 204) (nonnegative6766 p) (nonnegative5 p)
def d6768 (p : Pattern) : Int := if p 182 then d12 p else d6767 p
theorem agree6768 (p q : Pattern) (h : Agree support p q) : d6768 p = d6768 q := by
  simp only [d6768, h 182 (by decide), agree12 p q h, agree6767 p q h]
theorem nonnegative6768 (p : Pattern) : 0 ≤ d6768 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6767 p)
def d6769 (p : Pattern) : Int := if p 163 then d6768 p else d6762 p
theorem agree6769 (p q : Pattern) (h : Agree support p q) : d6769 p = d6769 q := by
  simp only [d6769, h 163 (by decide), agree6768 p q h, agree6762 p q h]
theorem nonnegative6769 (p : Pattern) : 0 ≤ d6769 p :=
  nonnegative_ite (p 163) (nonnegative6768 p) (nonnegative6762 p)
def d6770 (p : Pattern) : Int := if p 162 then d6769 p else d6761 p
theorem agree6770 (p q : Pattern) (h : Agree support p q) : d6770 p = d6770 q := by
  simp only [d6770, h 162 (by decide), agree6769 p q h, agree6761 p q h]
theorem nonnegative6770 (p : Pattern) : 0 ≤ d6770 p :=
  nonnegative_ite (p 162) (nonnegative6769 p) (nonnegative6761 p)
def d6771 (p : Pattern) : Int := if p 163 then d12 p else d6657 p
theorem agree6771 (p q : Pattern) (h : Agree support p q) : d6771 p = d6771 q := by
  simp only [d6771, h 163 (by decide), agree12 p q h, agree6657 p q h]
theorem nonnegative6771 (p : Pattern) : 0 ≤ d6771 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6657 p)
def d6772 (p : Pattern) : Int := if p 162 then d6771 p else d6769 p
theorem agree6772 (p q : Pattern) (h : Agree support p q) : d6772 p = d6772 q := by
  simp only [d6772, h 162 (by decide), agree6771 p q h, agree6769 p q h]
theorem nonnegative6772 (p : Pattern) : 0 ≤ d6772 p :=
  nonnegative_ite (p 162) (nonnegative6771 p) (nonnegative6769 p)
def d6773 (p : Pattern) : Int := if p 161 then d6772 p else d6770 p
theorem agree6773 (p q : Pattern) (h : Agree support p q) : d6773 p = d6773 q := by
  simp only [d6773, h 161 (by decide), agree6772 p q h, agree6770 p q h]
theorem nonnegative6773 (p : Pattern) : 0 ≤ d6773 p :=
  nonnegative_ite (p 161) (nonnegative6772 p) (nonnegative6770 p)
def d6774 (p : Pattern) : Int := if p 160 then d6773 p else d6741 p
theorem agree6774 (p q : Pattern) (h : Agree support p q) : d6774 p = d6774 q := by
  simp only [d6774, h 160 (by decide), agree6773 p q h, agree6741 p q h]
theorem nonnegative6774 (p : Pattern) : 0 ≤ d6774 p :=
  nonnegative_ite (p 160) (nonnegative6773 p) (nonnegative6741 p)
def d6775 (p : Pattern) : Int := if p 225 then d6750 p else d3 p
theorem agree6775 (p q : Pattern) (h : Agree support p q) : d6775 p = d6775 q := by
  simp only [d6775, h 225 (by decide), agree6750 p q h, agree3 p q h]
theorem nonnegative6775 (p : Pattern) : 0 ≤ d6775 p :=
  nonnegative_ite (p 225) (nonnegative6750 p) (nonnegative3 p)
def d6776 (p : Pattern) : Int := if p 224 then d6750 p else d6775 p
theorem agree6776 (p q : Pattern) (h : Agree support p q) : d6776 p = d6776 q := by
  simp only [d6776, h 224 (by decide), agree6750 p q h, agree6775 p q h]
theorem nonnegative6776 (p : Pattern) : 0 ≤ d6776 p :=
  nonnegative_ite (p 224) (nonnegative6750 p) (nonnegative6775 p)
def d6777 (p : Pattern) : Int := if p 204 then d6776 p else d3 p
theorem agree6777 (p q : Pattern) (h : Agree support p q) : d6777 p = d6777 q := by
  simp only [d6777, h 204 (by decide), agree6776 p q h, agree3 p q h]
theorem nonnegative6777 (p : Pattern) : 0 ≤ d6777 p :=
  nonnegative_ite (p 204) (nonnegative6776 p) (nonnegative3 p)
def d6778 (p : Pattern) : Int := if p 246 then d5 p else d3 p
theorem agree6778 (p q : Pattern) (h : Agree support p q) : d6778 p = d6778 q := by
  simp only [d6778, h 246 (by decide), agree5 p q h, agree3 p q h]
theorem nonnegative6778 (p : Pattern) : 0 ≤ d6778 p :=
  nonnegative_ite (p 246) (nonnegative5 p) (nonnegative3 p)
def d6779 (p : Pattern) : Int := if p 225 then d6778 p else d3 p
theorem agree6779 (p q : Pattern) (h : Agree support p q) : d6779 p = d6779 q := by
  simp only [d6779, h 225 (by decide), agree6778 p q h, agree3 p q h]
theorem nonnegative6779 (p : Pattern) : 0 ≤ d6779 p :=
  nonnegative_ite (p 225) (nonnegative6778 p) (nonnegative3 p)
def d6780 (p : Pattern) : Int := if p 224 then d6778 p else d6779 p
theorem agree6780 (p q : Pattern) (h : Agree support p q) : d6780 p = d6780 q := by
  simp only [d6780, h 224 (by decide), agree6778 p q h, agree6779 p q h]
theorem nonnegative6780 (p : Pattern) : 0 ≤ d6780 p :=
  nonnegative_ite (p 224) (nonnegative6778 p) (nonnegative6779 p)
def d6781 (p : Pattern) : Int := if p 204 then d12 p else d6780 p
theorem agree6781 (p q : Pattern) (h : Agree support p q) : d6781 p = d6781 q := by
  simp only [d6781, h 204 (by decide), agree12 p q h, agree6780 p q h]
theorem nonnegative6781 (p : Pattern) : 0 ≤ d6781 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6780 p)
def d6782 (p : Pattern) : Int := if p 182 then d6781 p else d6777 p
theorem agree6782 (p q : Pattern) (h : Agree support p q) : d6782 p = d6782 q := by
  simp only [d6782, h 182 (by decide), agree6781 p q h, agree6777 p q h]
theorem nonnegative6782 (p : Pattern) : 0 ≤ d6782 p :=
  nonnegative_ite (p 182) (nonnegative6781 p) (nonnegative6777 p)
def d6783 (p : Pattern) : Int := if p 163 then d6782 p else d6727 p
theorem agree6783 (p q : Pattern) (h : Agree support p q) : d6783 p = d6783 q := by
  simp only [d6783, h 163 (by decide), agree6782 p q h, agree6727 p q h]
theorem nonnegative6783 (p : Pattern) : 0 ≤ d6783 p :=
  nonnegative_ite (p 163) (nonnegative6782 p) (nonnegative6727 p)
def d6784 (p : Pattern) : Int := if p 163 then d6645 p else d6736 p
theorem agree6784 (p q : Pattern) (h : Agree support p q) : d6784 p = d6784 q := by
  simp only [d6784, h 163 (by decide), agree6645 p q h, agree6736 p q h]
theorem nonnegative6784 (p : Pattern) : 0 ≤ d6784 p :=
  nonnegative_ite (p 163) (nonnegative6645 p) (nonnegative6736 p)
def d6785 (p : Pattern) : Int := if p 162 then d6784 p else d6783 p
theorem agree6785 (p q : Pattern) (h : Agree support p q) : d6785 p = d6785 q := by
  simp only [d6785, h 162 (by decide), agree6784 p q h, agree6783 p q h]
theorem nonnegative6785 (p : Pattern) : 0 ≤ d6785 p :=
  nonnegative_ite (p 162) (nonnegative6784 p) (nonnegative6783 p)
def d6786 (p : Pattern) : Int := if p 163 then d6648 p else d6736 p
theorem agree6786 (p q : Pattern) (h : Agree support p q) : d6786 p = d6786 q := by
  simp only [d6786, h 163 (by decide), agree6648 p q h, agree6736 p q h]
theorem nonnegative6786 (p : Pattern) : 0 ≤ d6786 p :=
  nonnegative_ite (p 163) (nonnegative6648 p) (nonnegative6736 p)
def d6787 (p : Pattern) : Int := if p 162 then d12 p else d6786 p
theorem agree6787 (p q : Pattern) (h : Agree support p q) : d6787 p = d6787 q := by
  simp only [d6787, h 162 (by decide), agree12 p q h, agree6786 p q h]
theorem nonnegative6787 (p : Pattern) : 0 ≤ d6787 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6786 p)
def d6788 (p : Pattern) : Int := if p 161 then d6787 p else d6785 p
theorem agree6788 (p q : Pattern) (h : Agree support p q) : d6788 p = d6788 q := by
  simp only [d6788, h 161 (by decide), agree6787 p q h, agree6785 p q h]
theorem nonnegative6788 (p : Pattern) : 0 ≤ d6788 p :=
  nonnegative_ite (p 161) (nonnegative6787 p) (nonnegative6785 p)
def d6789 (p : Pattern) : Int := if p 204 then d6752 p else d3 p
theorem agree6789 (p q : Pattern) (h : Agree support p q) : d6789 p = d6789 q := by
  simp only [d6789, h 204 (by decide), agree6752 p q h, agree3 p q h]
theorem nonnegative6789 (p : Pattern) : 0 ≤ d6789 p :=
  nonnegative_ite (p 204) (nonnegative6752 p) (nonnegative3 p)
def d6790 (p : Pattern) : Int := if p 182 then d12 p else d6789 p
theorem agree6790 (p q : Pattern) (h : Agree support p q) : d6790 p = d6790 q := by
  simp only [d6790, h 182 (by decide), agree12 p q h, agree6789 p q h]
theorem nonnegative6790 (p : Pattern) : 0 ≤ d6790 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6789 p)
def d6791 (p : Pattern) : Int := if p 163 then d6790 p else d6760 p
theorem agree6791 (p q : Pattern) (h : Agree support p q) : d6791 p = d6791 q := by
  simp only [d6791, h 163 (by decide), agree6790 p q h, agree6760 p q h]
theorem nonnegative6791 (p : Pattern) : 0 ≤ d6791 p :=
  nonnegative_ite (p 163) (nonnegative6790 p) (nonnegative6760 p)
def d6792 (p : Pattern) : Int := if p 163 then d6657 p else d6768 p
theorem agree6792 (p q : Pattern) (h : Agree support p q) : d6792 p = d6792 q := by
  simp only [d6792, h 163 (by decide), agree6657 p q h, agree6768 p q h]
theorem nonnegative6792 (p : Pattern) : 0 ≤ d6792 p :=
  nonnegative_ite (p 163) (nonnegative6657 p) (nonnegative6768 p)
def d6793 (p : Pattern) : Int := if p 162 then d6792 p else d6791 p
theorem agree6793 (p q : Pattern) (h : Agree support p q) : d6793 p = d6793 q := by
  simp only [d6793, h 162 (by decide), agree6792 p q h, agree6791 p q h]
theorem nonnegative6793 (p : Pattern) : 0 ≤ d6793 p :=
  nonnegative_ite (p 162) (nonnegative6792 p) (nonnegative6791 p)
def d6794 (p : Pattern) : Int := if p 163 then d6659 p else d6768 p
theorem agree6794 (p q : Pattern) (h : Agree support p q) : d6794 p = d6794 q := by
  simp only [d6794, h 163 (by decide), agree6659 p q h, agree6768 p q h]
theorem nonnegative6794 (p : Pattern) : 0 ≤ d6794 p :=
  nonnegative_ite (p 163) (nonnegative6659 p) (nonnegative6768 p)
def d6795 (p : Pattern) : Int := if p 162 then d12 p else d6794 p
theorem agree6795 (p q : Pattern) (h : Agree support p q) : d6795 p = d6795 q := by
  simp only [d6795, h 162 (by decide), agree12 p q h, agree6794 p q h]
theorem nonnegative6795 (p : Pattern) : 0 ≤ d6795 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6794 p)
def d6796 (p : Pattern) : Int := if p 161 then d6795 p else d6793 p
theorem agree6796 (p q : Pattern) (h : Agree support p q) : d6796 p = d6796 q := by
  simp only [d6796, h 161 (by decide), agree6795 p q h, agree6793 p q h]
theorem nonnegative6796 (p : Pattern) : 0 ≤ d6796 p :=
  nonnegative_ite (p 161) (nonnegative6795 p) (nonnegative6793 p)
def d6797 (p : Pattern) : Int := if p 160 then d6796 p else d6788 p
theorem agree6797 (p q : Pattern) (h : Agree support p q) : d6797 p = d6797 q := by
  simp only [d6797, h 160 (by decide), agree6796 p q h, agree6788 p q h]
theorem nonnegative6797 (p : Pattern) : 0 ≤ d6797 p :=
  nonnegative_ite (p 160) (nonnegative6796 p) (nonnegative6788 p)
def d6798 (p : Pattern) : Int := if p 141 then d6797 p else d6774 p
theorem agree6798 (p q : Pattern) (h : Agree support p q) : d6798 p = d6798 q := by
  simp only [d6798, h 141 (by decide), agree6797 p q h, agree6774 p q h]
theorem nonnegative6798 (p : Pattern) : 0 ≤ d6798 p :=
  nonnegative_ite (p 141) (nonnegative6797 p) (nonnegative6774 p)
def d6799 (p : Pattern) : Int := if p 225 then d6742 p else d6719 p
theorem agree6799 (p q : Pattern) (h : Agree support p q) : d6799 p = d6799 q := by
  simp only [d6799, h 225 (by decide), agree6742 p q h, agree6719 p q h]
theorem nonnegative6799 (p : Pattern) : 0 ≤ d6799 p :=
  nonnegative_ite (p 225) (nonnegative6742 p) (nonnegative6719 p)
def d6800 (p : Pattern) : Int := if p 224 then d6799 p else d6743 p
theorem agree6800 (p q : Pattern) (h : Agree support p q) : d6800 p = d6800 q := by
  simp only [d6800, h 224 (by decide), agree6799 p q h, agree6743 p q h]
theorem nonnegative6800 (p : Pattern) : 0 ≤ d6800 p :=
  nonnegative_ite (p 224) (nonnegative6799 p) (nonnegative6743 p)
def d6801 (p : Pattern) : Int := if p 204 then d6800 p else d1 p
theorem agree6801 (p q : Pattern) (h : Agree support p q) : d6801 p = d6801 q := by
  simp only [d6801, h 204 (by decide), agree6800 p q h, agree1 p q h]
theorem nonnegative6801 (p : Pattern) : 0 ≤ d6801 p :=
  nonnegative_ite (p 204) (nonnegative6800 p) (nonnegative1 p)
def d6802 (p : Pattern) : Int := if p 204 then d12 p else d6721 p
theorem agree6802 (p q : Pattern) (h : Agree support p q) : d6802 p = d6802 q := by
  simp only [d6802, h 204 (by decide), agree12 p q h, agree6721 p q h]
theorem nonnegative6802 (p : Pattern) : 0 ≤ d6802 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6721 p)
def d6803 (p : Pattern) : Int := if p 182 then d6802 p else d6801 p
theorem agree6803 (p q : Pattern) (h : Agree support p q) : d6803 p = d6803 q := by
  simp only [d6803, h 182 (by decide), agree6802 p q h, agree6801 p q h]
theorem nonnegative6803 (p : Pattern) : 0 ≤ d6803 p :=
  nonnegative_ite (p 182) (nonnegative6802 p) (nonnegative6801 p)
def d6804 (p : Pattern) : Int := if p 246 then d9 p else d1 p
theorem agree6804 (p q : Pattern) (h : Agree support p q) : d6804 p = d6804 q := by
  simp only [d6804, h 246 (by decide), agree9 p q h, agree1 p q h]
theorem nonnegative6804 (p : Pattern) : 0 ≤ d6804 p :=
  nonnegative_ite (p 246) (nonnegative9 p) (nonnegative1 p)
def d6805 (p : Pattern) : Int := if p 225 then d6804 p else d6719 p
theorem agree6805 (p q : Pattern) (h : Agree support p q) : d6805 p = d6805 q := by
  simp only [d6805, h 225 (by decide), agree6804 p q h, agree6719 p q h]
theorem nonnegative6805 (p : Pattern) : 0 ≤ d6805 p :=
  nonnegative_ite (p 225) (nonnegative6804 p) (nonnegative6719 p)
def d6806 (p : Pattern) : Int := if p 224 then d6805 p else d6743 p
theorem agree6806 (p q : Pattern) (h : Agree support p q) : d6806 p = d6806 q := by
  simp only [d6806, h 224 (by decide), agree6805 p q h, agree6743 p q h]
theorem nonnegative6806 (p : Pattern) : 0 ≤ d6806 p :=
  nonnegative_ite (p 224) (nonnegative6805 p) (nonnegative6743 p)
def d6807 (p : Pattern) : Int := if p 204 then d12 p else d6806 p
theorem agree6807 (p q : Pattern) (h : Agree support p q) : d6807 p = d6807 q := by
  simp only [d6807, h 204 (by decide), agree12 p q h, agree6806 p q h]
theorem nonnegative6807 (p : Pattern) : 0 ≤ d6807 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6806 p)
def d6808 (p : Pattern) : Int := if p 182 then d6807 p else d6747 p
theorem agree6808 (p q : Pattern) (h : Agree support p q) : d6808 p = d6808 q := by
  simp only [d6808, h 182 (by decide), agree6807 p q h, agree6747 p q h]
theorem nonnegative6808 (p : Pattern) : 0 ≤ d6808 p :=
  nonnegative_ite (p 182) (nonnegative6807 p) (nonnegative6747 p)
def d6809 (p : Pattern) : Int := if p 163 then d6808 p else d6803 p
theorem agree6809 (p q : Pattern) (h : Agree support p q) : d6809 p = d6809 q := by
  simp only [d6809, h 163 (by decide), agree6808 p q h, agree6803 p q h]
theorem nonnegative6809 (p : Pattern) : 0 ≤ d6809 p :=
  nonnegative_ite (p 163) (nonnegative6808 p) (nonnegative6803 p)
def d6810 (p : Pattern) : Int := if p 204 then d12 p else d6746 p
theorem agree6810 (p q : Pattern) (h : Agree support p q) : d6810 p = d6810 q := by
  simp only [d6810, h 204 (by decide), agree12 p q h, agree6746 p q h]
theorem nonnegative6810 (p : Pattern) : 0 ≤ d6810 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6746 p)
def d6811 (p : Pattern) : Int := if p 182 then d6810 p else d6747 p
theorem agree6811 (p q : Pattern) (h : Agree support p q) : d6811 p = d6811 q := by
  simp only [d6811, h 182 (by decide), agree6810 p q h, agree6747 p q h]
theorem nonnegative6811 (p : Pattern) : 0 ≤ d6811 p :=
  nonnegative_ite (p 182) (nonnegative6810 p) (nonnegative6747 p)
def d6812 (p : Pattern) : Int := if p 204 then d12 p else d6766 p
theorem agree6812 (p q : Pattern) (h : Agree support p q) : d6812 p = d6812 q := by
  simp only [d6812, h 204 (by decide), agree12 p q h, agree6766 p q h]
theorem nonnegative6812 (p : Pattern) : 0 ≤ d6812 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6766 p)
def d6813 (p : Pattern) : Int := if p 182 then d6812 p else d6767 p
theorem agree6813 (p q : Pattern) (h : Agree support p q) : d6813 p = d6813 q := by
  simp only [d6813, h 182 (by decide), agree6812 p q h, agree6767 p q h]
theorem nonnegative6813 (p : Pattern) : 0 ≤ d6813 p :=
  nonnegative_ite (p 182) (nonnegative6812 p) (nonnegative6767 p)
def d6814 (p : Pattern) : Int := if p 163 then d6813 p else d6811 p
theorem agree6814 (p q : Pattern) (h : Agree support p q) : d6814 p = d6814 q := by
  simp only [d6814, h 163 (by decide), agree6813 p q h, agree6811 p q h]
theorem nonnegative6814 (p : Pattern) : 0 ≤ d6814 p :=
  nonnegative_ite (p 163) (nonnegative6813 p) (nonnegative6811 p)
def d6815 (p : Pattern) : Int := if p 162 then d6814 p else d6809 p
theorem agree6815 (p q : Pattern) (h : Agree support p q) : d6815 p = d6815 q := by
  simp only [d6815, h 162 (by decide), agree6814 p q h, agree6809 p q h]
theorem nonnegative6815 (p : Pattern) : 0 ≤ d6815 p :=
  nonnegative_ite (p 162) (nonnegative6814 p) (nonnegative6809 p)
def d6816 (p : Pattern) : Int := if p 162 then d6739 p else d6814 p
theorem agree6816 (p q : Pattern) (h : Agree support p q) : d6816 p = d6816 q := by
  simp only [d6816, h 162 (by decide), agree6739 p q h, agree6814 p q h]
theorem nonnegative6816 (p : Pattern) : 0 ≤ d6816 p :=
  nonnegative_ite (p 162) (nonnegative6739 p) (nonnegative6814 p)
def d6817 (p : Pattern) : Int := if p 161 then d6816 p else d6815 p
theorem agree6817 (p q : Pattern) (h : Agree support p q) : d6817 p = d6817 q := by
  simp only [d6817, h 161 (by decide), agree6816 p q h, agree6815 p q h]
theorem nonnegative6817 (p : Pattern) : 0 ≤ d6817 p :=
  nonnegative_ite (p 161) (nonnegative6816 p) (nonnegative6815 p)
def d6818 (p : Pattern) : Int := if p 182 then d6753 p else d6789 p
theorem agree6818 (p q : Pattern) (h : Agree support p q) : d6818 p = d6818 q := by
  simp only [d6818, h 182 (by decide), agree6753 p q h, agree6789 p q h]
theorem nonnegative6818 (p : Pattern) : 0 ≤ d6818 p :=
  nonnegative_ite (p 182) (nonnegative6753 p) (nonnegative6789 p)
def d6819 (p : Pattern) : Int := if p 204 then d6758 p else d7 p
theorem agree6819 (p q : Pattern) (h : Agree support p q) : d6819 p = d6819 q := by
  simp only [d6819, h 204 (by decide), agree6758 p q h, agree7 p q h]
theorem nonnegative6819 (p : Pattern) : 0 ≤ d6819 p :=
  nonnegative_ite (p 204) (nonnegative6758 p) (nonnegative7 p)
def d6820 (p : Pattern) : Int := if p 182 then d6759 p else d6819 p
theorem agree6820 (p q : Pattern) (h : Agree support p q) : d6820 p = d6820 q := by
  simp only [d6820, h 182 (by decide), agree6759 p q h, agree6819 p q h]
theorem nonnegative6820 (p : Pattern) : 0 ≤ d6820 p :=
  nonnegative_ite (p 182) (nonnegative6759 p) (nonnegative6819 p)
def d6821 (p : Pattern) : Int := if p 163 then d6820 p else d6818 p
theorem agree6821 (p q : Pattern) (h : Agree support p q) : d6821 p = d6821 q := by
  simp only [d6821, h 163 (by decide), agree6820 p q h, agree6818 p q h]
theorem nonnegative6821 (p : Pattern) : 0 ≤ d6821 p :=
  nonnegative_ite (p 163) (nonnegative6820 p) (nonnegative6818 p)
def d6822 (p : Pattern) : Int := if p 162 then d12 p else d6821 p
theorem agree6822 (p q : Pattern) (h : Agree support p q) : d6822 p = d6822 q := by
  simp only [d6822, h 162 (by decide), agree12 p q h, agree6821 p q h]
theorem nonnegative6822 (p : Pattern) : 0 ≤ d6822 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6821 p)
def d6823 (p : Pattern) : Int := if p 161 then d12 p else d6822 p
theorem agree6823 (p q : Pattern) (h : Agree support p q) : d6823 p = d6823 q := by
  simp only [d6823, h 161 (by decide), agree12 p q h, agree6822 p q h]
theorem nonnegative6823 (p : Pattern) : 0 ≤ d6823 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6822 p)
def d6824 (p : Pattern) : Int := if p 160 then d6823 p else d6817 p
theorem agree6824 (p q : Pattern) (h : Agree support p q) : d6824 p = d6824 q := by
  simp only [d6824, h 160 (by decide), agree6823 p q h, agree6817 p q h]
theorem nonnegative6824 (p : Pattern) : 0 ≤ d6824 p :=
  nonnegative_ite (p 160) (nonnegative6823 p) (nonnegative6817 p)
def d6825 (p : Pattern) : Int := if p 163 then d6818 p else d6808 p
theorem agree6825 (p q : Pattern) (h : Agree support p q) : d6825 p = d6825 q := by
  simp only [d6825, h 163 (by decide), agree6818 p q h, agree6808 p q h]
theorem nonnegative6825 (p : Pattern) : 0 ≤ d6825 p :=
  nonnegative_ite (p 163) (nonnegative6818 p) (nonnegative6808 p)
def d6826 (p : Pattern) : Int := if p 163 then d6645 p else d6813 p
theorem agree6826 (p q : Pattern) (h : Agree support p q) : d6826 p = d6826 q := by
  simp only [d6826, h 163 (by decide), agree6645 p q h, agree6813 p q h]
theorem nonnegative6826 (p : Pattern) : 0 ≤ d6826 p :=
  nonnegative_ite (p 163) (nonnegative6645 p) (nonnegative6813 p)
def d6827 (p : Pattern) : Int := if p 162 then d6826 p else d6825 p
theorem agree6827 (p q : Pattern) (h : Agree support p q) : d6827 p = d6827 q := by
  simp only [d6827, h 162 (by decide), agree6826 p q h, agree6825 p q h]
theorem nonnegative6827 (p : Pattern) : 0 ≤ d6827 p :=
  nonnegative_ite (p 162) (nonnegative6826 p) (nonnegative6825 p)
def d6828 (p : Pattern) : Int := if p 163 then d6648 p else d6813 p
theorem agree6828 (p q : Pattern) (h : Agree support p q) : d6828 p = d6828 q := by
  simp only [d6828, h 163 (by decide), agree6648 p q h, agree6813 p q h]
theorem nonnegative6828 (p : Pattern) : 0 ≤ d6828 p :=
  nonnegative_ite (p 163) (nonnegative6648 p) (nonnegative6813 p)
def d6829 (p : Pattern) : Int := if p 162 then d12 p else d6828 p
theorem agree6829 (p q : Pattern) (h : Agree support p q) : d6829 p = d6829 q := by
  simp only [d6829, h 162 (by decide), agree12 p q h, agree6828 p q h]
theorem nonnegative6829 (p : Pattern) : 0 ≤ d6829 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6828 p)
def d6830 (p : Pattern) : Int := if p 161 then d6829 p else d6827 p
theorem agree6830 (p q : Pattern) (h : Agree support p q) : d6830 p = d6830 q := by
  simp only [d6830, h 161 (by decide), agree6829 p q h, agree6827 p q h]
theorem nonnegative6830 (p : Pattern) : 0 ≤ d6830 p :=
  nonnegative_ite (p 161) (nonnegative6829 p) (nonnegative6827 p)
def d6831 (p : Pattern) : Int := if p 163 then d12 p else d6820 p
theorem agree6831 (p q : Pattern) (h : Agree support p q) : d6831 p = d6831 q := by
  simp only [d6831, h 163 (by decide), agree12 p q h, agree6820 p q h]
theorem nonnegative6831 (p : Pattern) : 0 ≤ d6831 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6820 p)
def d6832 (p : Pattern) : Int := if p 162 then d12 p else d6831 p
theorem agree6832 (p q : Pattern) (h : Agree support p q) : d6832 p = d6832 q := by
  simp only [d6832, h 162 (by decide), agree12 p q h, agree6831 p q h]
theorem nonnegative6832 (p : Pattern) : 0 ≤ d6832 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6831 p)
def d6833 (p : Pattern) : Int := if p 161 then d12 p else d6832 p
theorem agree6833 (p q : Pattern) (h : Agree support p q) : d6833 p = d6833 q := by
  simp only [d6833, h 161 (by decide), agree12 p q h, agree6832 p q h]
theorem nonnegative6833 (p : Pattern) : 0 ≤ d6833 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6832 p)
def d6834 (p : Pattern) : Int := if p 160 then d6833 p else d6830 p
theorem agree6834 (p q : Pattern) (h : Agree support p q) : d6834 p = d6834 q := by
  simp only [d6834, h 160 (by decide), agree6833 p q h, agree6830 p q h]
theorem nonnegative6834 (p : Pattern) : 0 ≤ d6834 p :=
  nonnegative_ite (p 160) (nonnegative6833 p) (nonnegative6830 p)
def d6835 (p : Pattern) : Int := if p 141 then d6834 p else d6824 p
theorem agree6835 (p q : Pattern) (h : Agree support p q) : d6835 p = d6835 q := by
  simp only [d6835, h 141 (by decide), agree6834 p q h, agree6824 p q h]
theorem nonnegative6835 (p : Pattern) : 0 ≤ d6835 p :=
  nonnegative_ite (p 141) (nonnegative6834 p) (nonnegative6824 p)
def d6836 (p : Pattern) : Int := if p 138 then d6835 p else d6798 p
theorem agree6836 (p q : Pattern) (h : Agree support p q) : d6836 p = d6836 q := by
  simp only [d6836, h 138 (by decide), agree6835 p q h, agree6798 p q h]
theorem nonnegative6836 (p : Pattern) : 0 ≤ d6836 p :=
  nonnegative_ite (p 138) (nonnegative6835 p) (nonnegative6798 p)
def d6837 (p : Pattern) : Int := if p 162 then d12 p else d6739 p
theorem agree6837 (p q : Pattern) (h : Agree support p q) : d6837 p = d6837 q := by
  simp only [d6837, h 162 (by decide), agree12 p q h, agree6739 p q h]
theorem nonnegative6837 (p : Pattern) : 0 ≤ d6837 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6739 p)
def d6838 (p : Pattern) : Int := if p 161 then d12 p else d6837 p
theorem agree6838 (p q : Pattern) (h : Agree support p q) : d6838 p = d6838 q := by
  simp only [d6838, h 161 (by decide), agree12 p q h, agree6837 p q h]
theorem nonnegative6838 (p : Pattern) : 0 ≤ d6838 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6837 p)
def d6839 (p : Pattern) : Int := if p 160 then d12 p else d6838 p
theorem agree6839 (p q : Pattern) (h : Agree support p q) : d6839 p = d6839 q := by
  simp only [d6839, h 160 (by decide), agree12 p q h, agree6838 p q h]
theorem nonnegative6839 (p : Pattern) : 0 ≤ d6839 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative6838 p)
end NetHack.Sokoban22Refined85
