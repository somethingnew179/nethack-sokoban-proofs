/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes46
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d5640 (p : Pattern) : Int := if p 163 then d5594 p else d5617 p
theorem agree5640 (p q : Pattern) (h : Agree support p q) : d5640 p = d5640 q := by
  simp only [d5640, h 163 (by decide), agree5594 p q h, agree5617 p q h]
theorem nonnegative5640 (p : Pattern) : 0 ≤ d5640 p :=
  nonnegative_ite (p 163) (nonnegative5594 p) (nonnegative5617 p)
def d5641 (p : Pattern) : Int := if p 162 then d5595 p else d5640 p
theorem agree5641 (p q : Pattern) (h : Agree support p q) : d5641 p = d5641 q := by
  simp only [d5641, h 162 (by decide), agree5595 p q h, agree5640 p q h]
theorem nonnegative5641 (p : Pattern) : 0 ≤ d5641 p :=
  nonnegative_ite (p 162) (nonnegative5595 p) (nonnegative5640 p)
def d5642 (p : Pattern) : Int := if p 162 then d12 p else d5595 p
theorem agree5642 (p q : Pattern) (h : Agree support p q) : d5642 p = d5642 q := by
  simp only [d5642, h 162 (by decide), agree12 p q h, agree5595 p q h]
theorem nonnegative5642 (p : Pattern) : 0 ≤ d5642 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5595 p)
def d5643 (p : Pattern) : Int := if p 161 then d5642 p else d5641 p
theorem agree5643 (p q : Pattern) (h : Agree support p q) : d5643 p = d5643 q := by
  simp only [d5643, h 161 (by decide), agree5642 p q h, agree5641 p q h]
theorem nonnegative5643 (p : Pattern) : 0 ≤ d5643 p :=
  nonnegative_ite (p 161) (nonnegative5642 p) (nonnegative5641 p)
def d5644 (p : Pattern) : Int := if p 161 then d12 p else d5642 p
theorem agree5644 (p q : Pattern) (h : Agree support p q) : d5644 p = d5644 q := by
  simp only [d5644, h 161 (by decide), agree12 p q h, agree5642 p q h]
theorem nonnegative5644 (p : Pattern) : 0 ≤ d5644 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5642 p)
def d5645 (p : Pattern) : Int := if p 160 then d5644 p else d5643 p
theorem agree5645 (p q : Pattern) (h : Agree support p q) : d5645 p = d5645 q := by
  simp only [d5645, h 160 (by decide), agree5644 p q h, agree5643 p q h]
theorem nonnegative5645 (p : Pattern) : 0 ≤ d5645 p :=
  nonnegative_ite (p 160) (nonnegative5644 p) (nonnegative5643 p)
def d5646 (p : Pattern) : Int := if p 160 then d12 p else d5644 p
theorem agree5646 (p q : Pattern) (h : Agree support p q) : d5646 p = d5646 q := by
  simp only [d5646, h 160 (by decide), agree12 p q h, agree5644 p q h]
theorem nonnegative5646 (p : Pattern) : 0 ≤ d5646 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative5644 p)
def d5647 (p : Pattern) : Int := if p 141 then d5646 p else d5645 p
theorem agree5647 (p q : Pattern) (h : Agree support p q) : d5647 p = d5647 q := by
  simp only [d5647, h 141 (by decide), agree5646 p q h, agree5645 p q h]
theorem nonnegative5647 (p : Pattern) : 0 ≤ d5647 p :=
  nonnegative_ite (p 141) (nonnegative5646 p) (nonnegative5645 p)
def d5648 (p : Pattern) : Int := if p 138 then d5647 p else d5638 p
theorem agree5648 (p q : Pattern) (h : Agree support p q) : d5648 p = d5648 q := by
  simp only [d5648, h 138 (by decide), agree5647 p q h, agree5638 p q h]
theorem nonnegative5648 (p : Pattern) : 0 ≤ d5648 p :=
  nonnegative_ite (p 138) (nonnegative5647 p) (nonnegative5638 p)
def d5649 (p : Pattern) : Int := if p 116 then d5648 p else d5639 p
theorem agree5649 (p q : Pattern) (h : Agree support p q) : d5649 p = d5649 q := by
  simp only [d5649, h 116 (by decide), agree5648 p q h, agree5639 p q h]
theorem nonnegative5649 (p : Pattern) : 0 ≤ d5649 p :=
  nonnegative_ite (p 116) (nonnegative5648 p) (nonnegative5639 p)
def d5650 (p : Pattern) : Int := if p 138 then d12 p else d5638 p
theorem agree5650 (p q : Pattern) (h : Agree support p q) : d5650 p = d5650 q := by
  simp only [d5650, h 138 (by decide), agree12 p q h, agree5638 p q h]
theorem nonnegative5650 (p : Pattern) : 0 ≤ d5650 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5638 p)
def d5651 (p : Pattern) : Int := if p 116 then d5650 p else d5639 p
theorem agree5651 (p q : Pattern) (h : Agree support p q) : d5651 p = d5651 q := by
  simp only [d5651, h 116 (by decide), agree5650 p q h, agree5639 p q h]
theorem nonnegative5651 (p : Pattern) : 0 ≤ d5651 p :=
  nonnegative_ite (p 116) (nonnegative5650 p) (nonnegative5639 p)
def d5652 (p : Pattern) : Int := if p 115 then d5651 p else d5649 p
theorem agree5652 (p q : Pattern) (h : Agree support p q) : d5652 p = d5652 q := by
  simp only [d5652, h 115 (by decide), agree5651 p q h, agree5649 p q h]
theorem nonnegative5652 (p : Pattern) : 0 ≤ d5652 p :=
  nonnegative_ite (p 115) (nonnegative5651 p) (nonnegative5649 p)
def d5653 (p : Pattern) : Int := if p 224 then d1940 p else d103 p
theorem agree5653 (p q : Pattern) (h : Agree support p q) : d5653 p = d5653 q := by
  simp only [d5653, h 224 (by decide), agree1940 p q h, agree103 p q h]
theorem nonnegative5653 (p : Pattern) : 0 ≤ d5653 p :=
  nonnegative_ite (p 224) (nonnegative1940 p) (nonnegative103 p)
def d5654 (p : Pattern) : Int := if p 204 then d5653 p else d103 p
theorem agree5654 (p q : Pattern) (h : Agree support p q) : d5654 p = d5654 q := by
  simp only [d5654, h 204 (by decide), agree5653 p q h, agree103 p q h]
theorem nonnegative5654 (p : Pattern) : 0 ≤ d5654 p :=
  nonnegative_ite (p 204) (nonnegative5653 p) (nonnegative103 p)
def d5655 (p : Pattern) : Int := if p 224 then d1873 p else d103 p
theorem agree5655 (p q : Pattern) (h : Agree support p q) : d5655 p = d5655 q := by
  simp only [d5655, h 224 (by decide), agree1873 p q h, agree103 p q h]
theorem nonnegative5655 (p : Pattern) : 0 ≤ d5655 p :=
  nonnegative_ite (p 224) (nonnegative1873 p) (nonnegative103 p)
def d5656 (p : Pattern) : Int := if p 204 then d12 p else d5655 p
theorem agree5656 (p q : Pattern) (h : Agree support p q) : d5656 p = d5656 q := by
  simp only [d5656, h 204 (by decide), agree12 p q h, agree5655 p q h]
theorem nonnegative5656 (p : Pattern) : 0 ≤ d5656 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5655 p)
def d5657 (p : Pattern) : Int := if p 182 then d5656 p else d5654 p
theorem agree5657 (p q : Pattern) (h : Agree support p q) : d5657 p = d5657 q := by
  simp only [d5657, h 182 (by decide), agree5656 p q h, agree5654 p q h]
theorem nonnegative5657 (p : Pattern) : 0 ≤ d5657 p :=
  nonnegative_ite (p 182) (nonnegative5656 p) (nonnegative5654 p)
def d5658 (p : Pattern) : Int := if p 224 then d1964 p else d107 p
theorem agree5658 (p q : Pattern) (h : Agree support p q) : d5658 p = d5658 q := by
  simp only [d5658, h 224 (by decide), agree1964 p q h, agree107 p q h]
theorem nonnegative5658 (p : Pattern) : 0 ≤ d5658 p :=
  nonnegative_ite (p 224) (nonnegative1964 p) (nonnegative107 p)
def d5659 (p : Pattern) : Int := if p 204 then d5658 p else d107 p
theorem agree5659 (p q : Pattern) (h : Agree support p q) : d5659 p = d5659 q := by
  simp only [d5659, h 204 (by decide), agree5658 p q h, agree107 p q h]
theorem nonnegative5659 (p : Pattern) : 0 ≤ d5659 p :=
  nonnegative_ite (p 204) (nonnegative5658 p) (nonnegative107 p)
def d5660 (p : Pattern) : Int := if p 224 then d1881 p else d107 p
theorem agree5660 (p q : Pattern) (h : Agree support p q) : d5660 p = d5660 q := by
  simp only [d5660, h 224 (by decide), agree1881 p q h, agree107 p q h]
theorem nonnegative5660 (p : Pattern) : 0 ≤ d5660 p :=
  nonnegative_ite (p 224) (nonnegative1881 p) (nonnegative107 p)
def d5661 (p : Pattern) : Int := if p 204 then d12 p else d5660 p
theorem agree5661 (p q : Pattern) (h : Agree support p q) : d5661 p = d5661 q := by
  simp only [d5661, h 204 (by decide), agree12 p q h, agree5660 p q h]
theorem nonnegative5661 (p : Pattern) : 0 ≤ d5661 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5660 p)
def d5662 (p : Pattern) : Int := if p 182 then d5661 p else d5659 p
theorem agree5662 (p q : Pattern) (h : Agree support p q) : d5662 p = d5662 q := by
  simp only [d5662, h 182 (by decide), agree5661 p q h, agree5659 p q h]
theorem nonnegative5662 (p : Pattern) : 0 ≤ d5662 p :=
  nonnegative_ite (p 182) (nonnegative5661 p) (nonnegative5659 p)
def d5663 (p : Pattern) : Int := if p 163 then d5662 p else d5657 p
theorem agree5663 (p q : Pattern) (h : Agree support p q) : d5663 p = d5663 q := by
  simp only [d5663, h 163 (by decide), agree5662 p q h, agree5657 p q h]
theorem nonnegative5663 (p : Pattern) : 0 ≤ d5663 p :=
  nonnegative_ite (p 163) (nonnegative5662 p) (nonnegative5657 p)
def d5664 (p : Pattern) : Int := if p 162 then d5663 p else d5657 p
theorem agree5664 (p q : Pattern) (h : Agree support p q) : d5664 p = d5664 q := by
  simp only [d5664, h 162 (by decide), agree5663 p q h, agree5657 p q h]
theorem nonnegative5664 (p : Pattern) : 0 ≤ d5664 p :=
  nonnegative_ite (p 162) (nonnegative5663 p) (nonnegative5657 p)
def d5665 (p : Pattern) : Int := if p 163 then d12 p else d5591 p
theorem agree5665 (p q : Pattern) (h : Agree support p q) : d5665 p = d5665 q := by
  simp only [d5665, h 163 (by decide), agree12 p q h, agree5591 p q h]
theorem nonnegative5665 (p : Pattern) : 0 ≤ d5665 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5591 p)
def d5666 (p : Pattern) : Int := if p 162 then d5665 p else d5663 p
theorem agree5666 (p q : Pattern) (h : Agree support p q) : d5666 p = d5666 q := by
  simp only [d5666, h 162 (by decide), agree5665 p q h, agree5663 p q h]
theorem nonnegative5666 (p : Pattern) : 0 ≤ d5666 p :=
  nonnegative_ite (p 162) (nonnegative5665 p) (nonnegative5663 p)
def d5667 (p : Pattern) : Int := if p 161 then d5666 p else d5664 p
theorem agree5667 (p q : Pattern) (h : Agree support p q) : d5667 p = d5667 q := by
  simp only [d5667, h 161 (by decide), agree5666 p q h, agree5664 p q h]
theorem nonnegative5667 (p : Pattern) : 0 ≤ d5667 p :=
  nonnegative_ite (p 161) (nonnegative5666 p) (nonnegative5664 p)
def d5668 (p : Pattern) : Int := if p 224 then d1895 p else d116 p
theorem agree5668 (p q : Pattern) (h : Agree support p q) : d5668 p = d5668 q := by
  simp only [d5668, h 224 (by decide), agree1895 p q h, agree116 p q h]
theorem nonnegative5668 (p : Pattern) : 0 ≤ d5668 p :=
  nonnegative_ite (p 224) (nonnegative1895 p) (nonnegative116 p)
def d5669 (p : Pattern) : Int := if p 204 then d12 p else d5668 p
theorem agree5669 (p q : Pattern) (h : Agree support p q) : d5669 p = d5669 q := by
  simp only [d5669, h 204 (by decide), agree12 p q h, agree5668 p q h]
theorem nonnegative5669 (p : Pattern) : 0 ≤ d5669 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5668 p)
def d5670 (p : Pattern) : Int := if p 182 then d5669 p else d5654 p
theorem agree5670 (p q : Pattern) (h : Agree support p q) : d5670 p = d5670 q := by
  simp only [d5670, h 182 (by decide), agree5669 p q h, agree5654 p q h]
theorem nonnegative5670 (p : Pattern) : 0 ≤ d5670 p :=
  nonnegative_ite (p 182) (nonnegative5669 p) (nonnegative5654 p)
def d5671 (p : Pattern) : Int := if p 224 then d1903 p else d120 p
theorem agree5671 (p q : Pattern) (h : Agree support p q) : d5671 p = d5671 q := by
  simp only [d5671, h 224 (by decide), agree1903 p q h, agree120 p q h]
theorem nonnegative5671 (p : Pattern) : 0 ≤ d5671 p :=
  nonnegative_ite (p 224) (nonnegative1903 p) (nonnegative120 p)
def d5672 (p : Pattern) : Int := if p 204 then d12 p else d5671 p
theorem agree5672 (p q : Pattern) (h : Agree support p q) : d5672 p = d5672 q := by
  simp only [d5672, h 204 (by decide), agree12 p q h, agree5671 p q h]
theorem nonnegative5672 (p : Pattern) : 0 ≤ d5672 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5671 p)
def d5673 (p : Pattern) : Int := if p 182 then d5672 p else d5654 p
theorem agree5673 (p q : Pattern) (h : Agree support p q) : d5673 p = d5673 q := by
  simp only [d5673, h 182 (by decide), agree5672 p q h, agree5654 p q h]
theorem nonnegative5673 (p : Pattern) : 0 ≤ d5673 p :=
  nonnegative_ite (p 182) (nonnegative5672 p) (nonnegative5654 p)
def d5674 (p : Pattern) : Int := if p 163 then d5673 p else d5670 p
theorem agree5674 (p q : Pattern) (h : Agree support p q) : d5674 p = d5674 q := by
  simp only [d5674, h 163 (by decide), agree5673 p q h, agree5670 p q h]
theorem nonnegative5674 (p : Pattern) : 0 ≤ d5674 p :=
  nonnegative_ite (p 163) (nonnegative5673 p) (nonnegative5670 p)
def d5675 (p : Pattern) : Int := if p 182 then d12 p else d5654 p
theorem agree5675 (p q : Pattern) (h : Agree support p q) : d5675 p = d5675 q := by
  simp only [d5675, h 182 (by decide), agree12 p q h, agree5654 p q h]
theorem nonnegative5675 (p : Pattern) : 0 ≤ d5675 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5654 p)
def d5676 (p : Pattern) : Int := if p 182 then d12 p else d5659 p
theorem agree5676 (p q : Pattern) (h : Agree support p q) : d5676 p = d5676 q := by
  simp only [d5676, h 182 (by decide), agree12 p q h, agree5659 p q h]
theorem nonnegative5676 (p : Pattern) : 0 ≤ d5676 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5659 p)
def d5677 (p : Pattern) : Int := if p 163 then d5676 p else d5675 p
theorem agree5677 (p q : Pattern) (h : Agree support p q) : d5677 p = d5677 q := by
  simp only [d5677, h 163 (by decide), agree5676 p q h, agree5675 p q h]
theorem nonnegative5677 (p : Pattern) : 0 ≤ d5677 p :=
  nonnegative_ite (p 163) (nonnegative5676 p) (nonnegative5675 p)
def d5678 (p : Pattern) : Int := if p 162 then d5677 p else d5674 p
theorem agree5678 (p q : Pattern) (h : Agree support p q) : d5678 p = d5678 q := by
  simp only [d5678, h 162 (by decide), agree5677 p q h, agree5674 p q h]
theorem nonnegative5678 (p : Pattern) : 0 ≤ d5678 p :=
  nonnegative_ite (p 162) (nonnegative5677 p) (nonnegative5674 p)
def d5679 (p : Pattern) : Int := if p 163 then d12 p else d5602 p
theorem agree5679 (p q : Pattern) (h : Agree support p q) : d5679 p = d5679 q := by
  simp only [d5679, h 163 (by decide), agree12 p q h, agree5602 p q h]
theorem nonnegative5679 (p : Pattern) : 0 ≤ d5679 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5602 p)
def d5680 (p : Pattern) : Int := if p 162 then d5679 p else d5677 p
theorem agree5680 (p q : Pattern) (h : Agree support p q) : d5680 p = d5680 q := by
  simp only [d5680, h 162 (by decide), agree5679 p q h, agree5677 p q h]
theorem nonnegative5680 (p : Pattern) : 0 ≤ d5680 p :=
  nonnegative_ite (p 162) (nonnegative5679 p) (nonnegative5677 p)
def d5681 (p : Pattern) : Int := if p 161 then d5680 p else d5678 p
theorem agree5681 (p q : Pattern) (h : Agree support p q) : d5681 p = d5681 q := by
  simp only [d5681, h 161 (by decide), agree5680 p q h, agree5678 p q h]
theorem nonnegative5681 (p : Pattern) : 0 ≤ d5681 p :=
  nonnegative_ite (p 161) (nonnegative5680 p) (nonnegative5678 p)
def d5682 (p : Pattern) : Int := if p 160 then d5681 p else d5667 p
theorem agree5682 (p q : Pattern) (h : Agree support p q) : d5682 p = d5682 q := by
  simp only [d5682, h 160 (by decide), agree5681 p q h, agree5667 p q h]
theorem nonnegative5682 (p : Pattern) : 0 ≤ d5682 p :=
  nonnegative_ite (p 160) (nonnegative5681 p) (nonnegative5667 p)
def d5683 (p : Pattern) : Int := if p 204 then d5668 p else d116 p
theorem agree5683 (p q : Pattern) (h : Agree support p q) : d5683 p = d5683 q := by
  simp only [d5683, h 204 (by decide), agree5668 p q h, agree116 p q h]
theorem nonnegative5683 (p : Pattern) : 0 ≤ d5683 p :=
  nonnegative_ite (p 204) (nonnegative5668 p) (nonnegative116 p)
def d5684 (p : Pattern) : Int := if p 224 then d1919 p else d116 p
theorem agree5684 (p q : Pattern) (h : Agree support p q) : d5684 p = d5684 q := by
  simp only [d5684, h 224 (by decide), agree1919 p q h, agree116 p q h]
theorem nonnegative5684 (p : Pattern) : 0 ≤ d5684 p :=
  nonnegative_ite (p 224) (nonnegative1919 p) (nonnegative116 p)
def d5685 (p : Pattern) : Int := if p 204 then d12 p else d5684 p
theorem agree5685 (p q : Pattern) (h : Agree support p q) : d5685 p = d5685 q := by
  simp only [d5685, h 204 (by decide), agree12 p q h, agree5684 p q h]
theorem nonnegative5685 (p : Pattern) : 0 ≤ d5685 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5684 p)
def d5686 (p : Pattern) : Int := if p 182 then d5685 p else d5683 p
theorem agree5686 (p q : Pattern) (h : Agree support p q) : d5686 p = d5686 q := by
  simp only [d5686, h 182 (by decide), agree5685 p q h, agree5683 p q h]
theorem nonnegative5686 (p : Pattern) : 0 ≤ d5686 p :=
  nonnegative_ite (p 182) (nonnegative5685 p) (nonnegative5683 p)
def d5687 (p : Pattern) : Int := if p 163 then d5686 p else d5657 p
theorem agree5687 (p q : Pattern) (h : Agree support p q) : d5687 p = d5687 q := by
  simp only [d5687, h 163 (by decide), agree5686 p q h, agree5657 p q h]
theorem nonnegative5687 (p : Pattern) : 0 ≤ d5687 p :=
  nonnegative_ite (p 163) (nonnegative5686 p) (nonnegative5657 p)
def d5688 (p : Pattern) : Int := if p 163 then d5591 p else d5662 p
theorem agree5688 (p q : Pattern) (h : Agree support p q) : d5688 p = d5688 q := by
  simp only [d5688, h 163 (by decide), agree5591 p q h, agree5662 p q h]
theorem nonnegative5688 (p : Pattern) : 0 ≤ d5688 p :=
  nonnegative_ite (p 163) (nonnegative5591 p) (nonnegative5662 p)
def d5689 (p : Pattern) : Int := if p 162 then d5688 p else d5687 p
theorem agree5689 (p q : Pattern) (h : Agree support p q) : d5689 p = d5689 q := by
  simp only [d5689, h 162 (by decide), agree5688 p q h, agree5687 p q h]
theorem nonnegative5689 (p : Pattern) : 0 ≤ d5689 p :=
  nonnegative_ite (p 162) (nonnegative5688 p) (nonnegative5687 p)
def d5690 (p : Pattern) : Int := if p 163 then d5594 p else d5662 p
theorem agree5690 (p q : Pattern) (h : Agree support p q) : d5690 p = d5690 q := by
  simp only [d5690, h 163 (by decide), agree5594 p q h, agree5662 p q h]
theorem nonnegative5690 (p : Pattern) : 0 ≤ d5690 p :=
  nonnegative_ite (p 163) (nonnegative5594 p) (nonnegative5662 p)
def d5691 (p : Pattern) : Int := if p 162 then d12 p else d5690 p
theorem agree5691 (p q : Pattern) (h : Agree support p q) : d5691 p = d5691 q := by
  simp only [d5691, h 162 (by decide), agree12 p q h, agree5690 p q h]
theorem nonnegative5691 (p : Pattern) : 0 ≤ d5691 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5690 p)
def d5692 (p : Pattern) : Int := if p 161 then d5691 p else d5689 p
theorem agree5692 (p q : Pattern) (h : Agree support p q) : d5692 p = d5692 q := by
  simp only [d5692, h 161 (by decide), agree5691 p q h, agree5689 p q h]
theorem nonnegative5692 (p : Pattern) : 0 ≤ d5692 p :=
  nonnegative_ite (p 161) (nonnegative5691 p) (nonnegative5689 p)
def d5693 (p : Pattern) : Int := if p 182 then d12 p else d5683 p
theorem agree5693 (p q : Pattern) (h : Agree support p q) : d5693 p = d5693 q := by
  simp only [d5693, h 182 (by decide), agree12 p q h, agree5683 p q h]
theorem nonnegative5693 (p : Pattern) : 0 ≤ d5693 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5683 p)
def d5694 (p : Pattern) : Int := if p 163 then d5693 p else d5673 p
theorem agree5694 (p q : Pattern) (h : Agree support p q) : d5694 p = d5694 q := by
  simp only [d5694, h 163 (by decide), agree5693 p q h, agree5673 p q h]
theorem nonnegative5694 (p : Pattern) : 0 ≤ d5694 p :=
  nonnegative_ite (p 163) (nonnegative5693 p) (nonnegative5673 p)
def d5695 (p : Pattern) : Int := if p 163 then d5602 p else d5676 p
theorem agree5695 (p q : Pattern) (h : Agree support p q) : d5695 p = d5695 q := by
  simp only [d5695, h 163 (by decide), agree5602 p q h, agree5676 p q h]
theorem nonnegative5695 (p : Pattern) : 0 ≤ d5695 p :=
  nonnegative_ite (p 163) (nonnegative5602 p) (nonnegative5676 p)
def d5696 (p : Pattern) : Int := if p 162 then d5695 p else d5694 p
theorem agree5696 (p q : Pattern) (h : Agree support p q) : d5696 p = d5696 q := by
  simp only [d5696, h 162 (by decide), agree5695 p q h, agree5694 p q h]
theorem nonnegative5696 (p : Pattern) : 0 ≤ d5696 p :=
  nonnegative_ite (p 162) (nonnegative5695 p) (nonnegative5694 p)
def d5697 (p : Pattern) : Int := if p 163 then d5604 p else d5676 p
theorem agree5697 (p q : Pattern) (h : Agree support p q) : d5697 p = d5697 q := by
  simp only [d5697, h 163 (by decide), agree5604 p q h, agree5676 p q h]
theorem nonnegative5697 (p : Pattern) : 0 ≤ d5697 p :=
  nonnegative_ite (p 163) (nonnegative5604 p) (nonnegative5676 p)
def d5698 (p : Pattern) : Int := if p 162 then d12 p else d5697 p
theorem agree5698 (p q : Pattern) (h : Agree support p q) : d5698 p = d5698 q := by
  simp only [d5698, h 162 (by decide), agree12 p q h, agree5697 p q h]
theorem nonnegative5698 (p : Pattern) : 0 ≤ d5698 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5697 p)
def d5699 (p : Pattern) : Int := if p 161 then d5698 p else d5696 p
theorem agree5699 (p q : Pattern) (h : Agree support p q) : d5699 p = d5699 q := by
  simp only [d5699, h 161 (by decide), agree5698 p q h, agree5696 p q h]
theorem nonnegative5699 (p : Pattern) : 0 ≤ d5699 p :=
  nonnegative_ite (p 161) (nonnegative5698 p) (nonnegative5696 p)
def d5700 (p : Pattern) : Int := if p 160 then d5699 p else d5692 p
theorem agree5700 (p q : Pattern) (h : Agree support p q) : d5700 p = d5700 q := by
  simp only [d5700, h 160 (by decide), agree5699 p q h, agree5692 p q h]
theorem nonnegative5700 (p : Pattern) : 0 ≤ d5700 p :=
  nonnegative_ite (p 160) (nonnegative5699 p) (nonnegative5692 p)
def d5701 (p : Pattern) : Int := if p 141 then d5700 p else d5682 p
theorem agree5701 (p q : Pattern) (h : Agree support p q) : d5701 p = d5701 q := by
  simp only [d5701, h 141 (by decide), agree5700 p q h, agree5682 p q h]
theorem nonnegative5701 (p : Pattern) : 0 ≤ d5701 p :=
  nonnegative_ite (p 141) (nonnegative5700 p) (nonnegative5682 p)
def d5702 (p : Pattern) : Int := if p 204 then d12 p else d5653 p
theorem agree5702 (p q : Pattern) (h : Agree support p q) : d5702 p = d5702 q := by
  simp only [d5702, h 204 (by decide), agree12 p q h, agree5653 p q h]
theorem nonnegative5702 (p : Pattern) : 0 ≤ d5702 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5653 p)
def d5703 (p : Pattern) : Int := if p 182 then d5702 p else d5654 p
theorem agree5703 (p q : Pattern) (h : Agree support p q) : d5703 p = d5703 q := by
  simp only [d5703, h 182 (by decide), agree5702 p q h, agree5654 p q h]
theorem nonnegative5703 (p : Pattern) : 0 ≤ d5703 p :=
  nonnegative_ite (p 182) (nonnegative5702 p) (nonnegative5654 p)
def d5704 (p : Pattern) : Int := if p 204 then d12 p else d5658 p
theorem agree5704 (p q : Pattern) (h : Agree support p q) : d5704 p = d5704 q := by
  simp only [d5704, h 204 (by decide), agree12 p q h, agree5658 p q h]
theorem nonnegative5704 (p : Pattern) : 0 ≤ d5704 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5658 p)
def d5705 (p : Pattern) : Int := if p 182 then d5704 p else d5659 p
theorem agree5705 (p q : Pattern) (h : Agree support p q) : d5705 p = d5705 q := by
  simp only [d5705, h 182 (by decide), agree5704 p q h, agree5659 p q h]
theorem nonnegative5705 (p : Pattern) : 0 ≤ d5705 p :=
  nonnegative_ite (p 182) (nonnegative5704 p) (nonnegative5659 p)
def d5706 (p : Pattern) : Int := if p 163 then d5705 p else d5703 p
theorem agree5706 (p q : Pattern) (h : Agree support p q) : d5706 p = d5706 q := by
  simp only [d5706, h 163 (by decide), agree5705 p q h, agree5703 p q h]
theorem nonnegative5706 (p : Pattern) : 0 ≤ d5706 p :=
  nonnegative_ite (p 163) (nonnegative5705 p) (nonnegative5703 p)
def d5707 (p : Pattern) : Int := if p 162 then d5706 p else d5703 p
theorem agree5707 (p q : Pattern) (h : Agree support p q) : d5707 p = d5707 q := by
  simp only [d5707, h 162 (by decide), agree5706 p q h, agree5703 p q h]
theorem nonnegative5707 (p : Pattern) : 0 ≤ d5707 p :=
  nonnegative_ite (p 162) (nonnegative5706 p) (nonnegative5703 p)
def d5708 (p : Pattern) : Int := if p 162 then d5665 p else d5706 p
theorem agree5708 (p q : Pattern) (h : Agree support p q) : d5708 p = d5708 q := by
  simp only [d5708, h 162 (by decide), agree5665 p q h, agree5706 p q h]
theorem nonnegative5708 (p : Pattern) : 0 ≤ d5708 p :=
  nonnegative_ite (p 162) (nonnegative5665 p) (nonnegative5706 p)
def d5709 (p : Pattern) : Int := if p 161 then d5708 p else d5707 p
theorem agree5709 (p q : Pattern) (h : Agree support p q) : d5709 p = d5709 q := by
  simp only [d5709, h 161 (by decide), agree5708 p q h, agree5707 p q h]
theorem nonnegative5709 (p : Pattern) : 0 ≤ d5709 p :=
  nonnegative_ite (p 161) (nonnegative5708 p) (nonnegative5707 p)
def d5710 (p : Pattern) : Int := if p 182 then d5669 p else d5683 p
theorem agree5710 (p q : Pattern) (h : Agree support p q) : d5710 p = d5710 q := by
  simp only [d5710, h 182 (by decide), agree5669 p q h, agree5683 p q h]
theorem nonnegative5710 (p : Pattern) : 0 ≤ d5710 p :=
  nonnegative_ite (p 182) (nonnegative5669 p) (nonnegative5683 p)
def d5711 (p : Pattern) : Int := if p 204 then d5671 p else d120 p
theorem agree5711 (p q : Pattern) (h : Agree support p q) : d5711 p = d5711 q := by
  simp only [d5711, h 204 (by decide), agree5671 p q h, agree120 p q h]
theorem nonnegative5711 (p : Pattern) : 0 ≤ d5711 p :=
  nonnegative_ite (p 204) (nonnegative5671 p) (nonnegative120 p)
def d5712 (p : Pattern) : Int := if p 182 then d5672 p else d5711 p
theorem agree5712 (p q : Pattern) (h : Agree support p q) : d5712 p = d5712 q := by
  simp only [d5712, h 182 (by decide), agree5672 p q h, agree5711 p q h]
theorem nonnegative5712 (p : Pattern) : 0 ≤ d5712 p :=
  nonnegative_ite (p 182) (nonnegative5672 p) (nonnegative5711 p)
def d5713 (p : Pattern) : Int := if p 163 then d5712 p else d5710 p
theorem agree5713 (p q : Pattern) (h : Agree support p q) : d5713 p = d5713 q := by
  simp only [d5713, h 163 (by decide), agree5712 p q h, agree5710 p q h]
theorem nonnegative5713 (p : Pattern) : 0 ≤ d5713 p :=
  nonnegative_ite (p 163) (nonnegative5712 p) (nonnegative5710 p)
def d5714 (p : Pattern) : Int := if p 162 then d12 p else d5713 p
theorem agree5714 (p q : Pattern) (h : Agree support p q) : d5714 p = d5714 q := by
  simp only [d5714, h 162 (by decide), agree12 p q h, agree5713 p q h]
theorem nonnegative5714 (p : Pattern) : 0 ≤ d5714 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5713 p)
def d5715 (p : Pattern) : Int := if p 161 then d12 p else d5714 p
theorem agree5715 (p q : Pattern) (h : Agree support p q) : d5715 p = d5715 q := by
  simp only [d5715, h 161 (by decide), agree12 p q h, agree5714 p q h]
theorem nonnegative5715 (p : Pattern) : 0 ≤ d5715 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5714 p)
def d5716 (p : Pattern) : Int := if p 160 then d5715 p else d5709 p
theorem agree5716 (p q : Pattern) (h : Agree support p q) : d5716 p = d5716 q := by
  simp only [d5716, h 160 (by decide), agree5715 p q h, agree5709 p q h]
theorem nonnegative5716 (p : Pattern) : 0 ≤ d5716 p :=
  nonnegative_ite (p 160) (nonnegative5715 p) (nonnegative5709 p)
def d5717 (p : Pattern) : Int := if p 163 then d5710 p else d5703 p
theorem agree5717 (p q : Pattern) (h : Agree support p q) : d5717 p = d5717 q := by
  simp only [d5717, h 163 (by decide), agree5710 p q h, agree5703 p q h]
theorem nonnegative5717 (p : Pattern) : 0 ≤ d5717 p :=
  nonnegative_ite (p 163) (nonnegative5710 p) (nonnegative5703 p)
def d5718 (p : Pattern) : Int := if p 163 then d5591 p else d5705 p
theorem agree5718 (p q : Pattern) (h : Agree support p q) : d5718 p = d5718 q := by
  simp only [d5718, h 163 (by decide), agree5591 p q h, agree5705 p q h]
theorem nonnegative5718 (p : Pattern) : 0 ≤ d5718 p :=
  nonnegative_ite (p 163) (nonnegative5591 p) (nonnegative5705 p)
def d5719 (p : Pattern) : Int := if p 162 then d5718 p else d5717 p
theorem agree5719 (p q : Pattern) (h : Agree support p q) : d5719 p = d5719 q := by
  simp only [d5719, h 162 (by decide), agree5718 p q h, agree5717 p q h]
theorem nonnegative5719 (p : Pattern) : 0 ≤ d5719 p :=
  nonnegative_ite (p 162) (nonnegative5718 p) (nonnegative5717 p)
def d5720 (p : Pattern) : Int := if p 163 then d5594 p else d5705 p
theorem agree5720 (p q : Pattern) (h : Agree support p q) : d5720 p = d5720 q := by
  simp only [d5720, h 163 (by decide), agree5594 p q h, agree5705 p q h]
theorem nonnegative5720 (p : Pattern) : 0 ≤ d5720 p :=
  nonnegative_ite (p 163) (nonnegative5594 p) (nonnegative5705 p)
def d5721 (p : Pattern) : Int := if p 162 then d12 p else d5720 p
theorem agree5721 (p q : Pattern) (h : Agree support p q) : d5721 p = d5721 q := by
  simp only [d5721, h 162 (by decide), agree12 p q h, agree5720 p q h]
theorem nonnegative5721 (p : Pattern) : 0 ≤ d5721 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5720 p)
def d5722 (p : Pattern) : Int := if p 161 then d5721 p else d5719 p
theorem agree5722 (p q : Pattern) (h : Agree support p q) : d5722 p = d5722 q := by
  simp only [d5722, h 161 (by decide), agree5721 p q h, agree5719 p q h]
theorem nonnegative5722 (p : Pattern) : 0 ≤ d5722 p :=
  nonnegative_ite (p 161) (nonnegative5721 p) (nonnegative5719 p)
def d5723 (p : Pattern) : Int := if p 163 then d12 p else d5712 p
theorem agree5723 (p q : Pattern) (h : Agree support p q) : d5723 p = d5723 q := by
  simp only [d5723, h 163 (by decide), agree12 p q h, agree5712 p q h]
theorem nonnegative5723 (p : Pattern) : 0 ≤ d5723 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5712 p)
def d5724 (p : Pattern) : Int := if p 162 then d12 p else d5723 p
theorem agree5724 (p q : Pattern) (h : Agree support p q) : d5724 p = d5724 q := by
  simp only [d5724, h 162 (by decide), agree12 p q h, agree5723 p q h]
theorem nonnegative5724 (p : Pattern) : 0 ≤ d5724 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5723 p)
def d5725 (p : Pattern) : Int := if p 161 then d12 p else d5724 p
theorem agree5725 (p q : Pattern) (h : Agree support p q) : d5725 p = d5725 q := by
  simp only [d5725, h 161 (by decide), agree12 p q h, agree5724 p q h]
theorem nonnegative5725 (p : Pattern) : 0 ≤ d5725 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5724 p)
def d5726 (p : Pattern) : Int := if p 160 then d5725 p else d5722 p
theorem agree5726 (p q : Pattern) (h : Agree support p q) : d5726 p = d5726 q := by
  simp only [d5726, h 160 (by decide), agree5725 p q h, agree5722 p q h]
theorem nonnegative5726 (p : Pattern) : 0 ≤ d5726 p :=
  nonnegative_ite (p 160) (nonnegative5725 p) (nonnegative5722 p)
def d5727 (p : Pattern) : Int := if p 141 then d5726 p else d5716 p
theorem agree5727 (p q : Pattern) (h : Agree support p q) : d5727 p = d5727 q := by
  simp only [d5727, h 141 (by decide), agree5726 p q h, agree5716 p q h]
theorem nonnegative5727 (p : Pattern) : 0 ≤ d5727 p :=
  nonnegative_ite (p 141) (nonnegative5726 p) (nonnegative5716 p)
def d5728 (p : Pattern) : Int := if p 138 then d5727 p else d5701 p
theorem agree5728 (p q : Pattern) (h : Agree support p q) : d5728 p = d5728 q := by
  simp only [d5728, h 138 (by decide), agree5727 p q h, agree5701 p q h]
theorem nonnegative5728 (p : Pattern) : 0 ≤ d5728 p :=
  nonnegative_ite (p 138) (nonnegative5727 p) (nonnegative5701 p)
def d5729 (p : Pattern) : Int := if p 162 then d12 p else d5665 p
theorem agree5729 (p q : Pattern) (h : Agree support p q) : d5729 p = d5729 q := by
  simp only [d5729, h 162 (by decide), agree12 p q h, agree5665 p q h]
theorem nonnegative5729 (p : Pattern) : 0 ≤ d5729 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5665 p)
def d5730 (p : Pattern) : Int := if p 161 then d12 p else d5729 p
theorem agree5730 (p q : Pattern) (h : Agree support p q) : d5730 p = d5730 q := by
  simp only [d5730, h 161 (by decide), agree12 p q h, agree5729 p q h]
theorem nonnegative5730 (p : Pattern) : 0 ≤ d5730 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5729 p)
def d5731 (p : Pattern) : Int := if p 160 then d12 p else d5730 p
theorem agree5731 (p q : Pattern) (h : Agree support p q) : d5731 p = d5731 q := by
  simp only [d5731, h 160 (by decide), agree12 p q h, agree5730 p q h]
theorem nonnegative5731 (p : Pattern) : 0 ≤ d5731 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative5730 p)
def d5732 (p : Pattern) : Int := if p 141 then d12 p else d5731 p
theorem agree5732 (p q : Pattern) (h : Agree support p q) : d5732 p = d5732 q := by
  simp only [d5732, h 141 (by decide), agree12 p q h, agree5731 p q h]
theorem nonnegative5732 (p : Pattern) : 0 ≤ d5732 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative5731 p)
def d5733 (p : Pattern) : Int := if p 138 then d5732 p else d5727 p
theorem agree5733 (p q : Pattern) (h : Agree support p q) : d5733 p = d5733 q := by
  simp only [d5733, h 138 (by decide), agree5732 p q h, agree5727 p q h]
theorem nonnegative5733 (p : Pattern) : 0 ≤ d5733 p :=
  nonnegative_ite (p 138) (nonnegative5732 p) (nonnegative5727 p)
def d5734 (p : Pattern) : Int := if p 116 then d5733 p else d5728 p
theorem agree5734 (p q : Pattern) (h : Agree support p q) : d5734 p = d5734 q := by
  simp only [d5734, h 116 (by decide), agree5733 p q h, agree5728 p q h]
theorem nonnegative5734 (p : Pattern) : 0 ≤ d5734 p :=
  nonnegative_ite (p 116) (nonnegative5733 p) (nonnegative5728 p)
def d5735 (p : Pattern) : Int := if p 138 then d12 p else d5727 p
theorem agree5735 (p q : Pattern) (h : Agree support p q) : d5735 p = d5735 q := by
  simp only [d5735, h 138 (by decide), agree12 p q h, agree5727 p q h]
theorem nonnegative5735 (p : Pattern) : 0 ≤ d5735 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5727 p)
def d5736 (p : Pattern) : Int := if p 116 then d5735 p else d5728 p
theorem agree5736 (p q : Pattern) (h : Agree support p q) : d5736 p = d5736 q := by
  simp only [d5736, h 116 (by decide), agree5735 p q h, agree5728 p q h]
theorem nonnegative5736 (p : Pattern) : 0 ≤ d5736 p :=
  nonnegative_ite (p 116) (nonnegative5735 p) (nonnegative5728 p)
def d5737 (p : Pattern) : Int := if p 115 then d5736 p else d5734 p
theorem agree5737 (p q : Pattern) (h : Agree support p q) : d5737 p = d5737 q := by
  simp only [d5737, h 115 (by decide), agree5736 p q h, agree5734 p q h]
theorem nonnegative5737 (p : Pattern) : 0 ≤ d5737 p :=
  nonnegative_ite (p 115) (nonnegative5736 p) (nonnegative5734 p)
def d5738 (p : Pattern) : Int := if p 71 then d5737 p else d5652 p
theorem agree5738 (p q : Pattern) (h : Agree support p q) : d5738 p = d5738 q := by
  simp only [d5738, h 71 (by decide), agree5737 p q h, agree5652 p q h]
theorem nonnegative5738 (p : Pattern) : 0 ≤ d5738 p :=
  nonnegative_ite (p 71) (nonnegative5737 p) (nonnegative5652 p)
def d5739 (p : Pattern) : Int := if p 49 then d5738 p else d5652 p
theorem agree5739 (p q : Pattern) (h : Agree support p q) : d5739 p = d5739 q := by
  simp only [d5739, h 49 (by decide), agree5738 p q h, agree5652 p q h]
theorem nonnegative5739 (p : Pattern) : 0 ≤ d5739 p :=
  nonnegative_ite (p 49) (nonnegative5738 p) (nonnegative5652 p)
def d5740 (p : Pattern) : Int := if p 182 then d5565 p else d5581 p
theorem agree5740 (p q : Pattern) (h : Agree support p q) : d5740 p = d5740 q := by
  simp only [d5740, h 182 (by decide), agree5565 p q h, agree5581 p q h]
theorem nonnegative5740 (p : Pattern) : 0 ≤ d5740 p :=
  nonnegative_ite (p 182) (nonnegative5565 p) (nonnegative5581 p)
def d5741 (p : Pattern) : Int := if p 163 then d5740 p else d5621 p
theorem agree5741 (p q : Pattern) (h : Agree support p q) : d5741 p = d5741 q := by
  simp only [d5741, h 163 (by decide), agree5740 p q h, agree5621 p q h]
theorem nonnegative5741 (p : Pattern) : 0 ≤ d5741 p :=
  nonnegative_ite (p 163) (nonnegative5740 p) (nonnegative5621 p)
def d5742 (p : Pattern) : Int := if p 182 then d5569 p else d5581 p
theorem agree5742 (p q : Pattern) (h : Agree support p q) : d5742 p = d5742 q := by
  simp only [d5742, h 182 (by decide), agree5569 p q h, agree5581 p q h]
theorem nonnegative5742 (p : Pattern) : 0 ≤ d5742 p :=
  nonnegative_ite (p 182) (nonnegative5569 p) (nonnegative5581 p)
def d5743 (p : Pattern) : Int := if p 182 then d12 p else d5622 p
theorem agree5743 (p q : Pattern) (h : Agree support p q) : d5743 p = d5743 q := by
  simp only [d5743, h 182 (by decide), agree12 p q h, agree5622 p q h]
theorem nonnegative5743 (p : Pattern) : 0 ≤ d5743 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5622 p)
def d5744 (p : Pattern) : Int := if p 163 then d5743 p else d5742 p
theorem agree5744 (p q : Pattern) (h : Agree support p q) : d5744 p = d5744 q := by
  simp only [d5744, h 163 (by decide), agree5743 p q h, agree5742 p q h]
theorem nonnegative5744 (p : Pattern) : 0 ≤ d5744 p :=
  nonnegative_ite (p 163) (nonnegative5743 p) (nonnegative5742 p)
def d5745 (p : Pattern) : Int := if p 162 then d5744 p else d5741 p
theorem agree5745 (p q : Pattern) (h : Agree support p q) : d5745 p = d5745 q := by
  simp only [d5745, h 162 (by decide), agree5744 p q h, agree5741 p q h]
theorem nonnegative5745 (p : Pattern) : 0 ≤ d5745 p :=
  nonnegative_ite (p 162) (nonnegative5744 p) (nonnegative5741 p)
def d5746 (p : Pattern) : Int := if p 163 then d5743 p else d5598 p
theorem agree5746 (p q : Pattern) (h : Agree support p q) : d5746 p = d5746 q := by
  simp only [d5746, h 163 (by decide), agree5743 p q h, agree5598 p q h]
theorem nonnegative5746 (p : Pattern) : 0 ≤ d5746 p :=
  nonnegative_ite (p 163) (nonnegative5743 p) (nonnegative5598 p)
def d5747 (p : Pattern) : Int := if p 162 then d5605 p else d5746 p
theorem agree5747 (p q : Pattern) (h : Agree support p q) : d5747 p = d5747 q := by
  simp only [d5747, h 162 (by decide), agree5605 p q h, agree5746 p q h]
theorem nonnegative5747 (p : Pattern) : 0 ≤ d5747 p :=
  nonnegative_ite (p 162) (nonnegative5605 p) (nonnegative5746 p)
def d5748 (p : Pattern) : Int := if p 161 then d5747 p else d5745 p
theorem agree5748 (p q : Pattern) (h : Agree support p q) : d5748 p = d5748 q := by
  simp only [d5748, h 161 (by decide), agree5747 p q h, agree5745 p q h]
theorem nonnegative5748 (p : Pattern) : 0 ≤ d5748 p :=
  nonnegative_ite (p 161) (nonnegative5747 p) (nonnegative5745 p)
def d5749 (p : Pattern) : Int := if p 160 then d5748 p else d5620 p
theorem agree5749 (p q : Pattern) (h : Agree support p q) : d5749 p = d5749 q := by
  simp only [d5749, h 160 (by decide), agree5748 p q h, agree5620 p q h]
theorem nonnegative5749 (p : Pattern) : 0 ≤ d5749 p :=
  nonnegative_ite (p 160) (nonnegative5748 p) (nonnegative5620 p)
def d5750 (p : Pattern) : Int := if p 163 then d5571 p else d5740 p
theorem agree5750 (p q : Pattern) (h : Agree support p q) : d5750 p = d5750 q := by
  simp only [d5750, h 163 (by decide), agree5571 p q h, agree5740 p q h]
theorem nonnegative5750 (p : Pattern) : 0 ≤ d5750 p :=
  nonnegative_ite (p 163) (nonnegative5571 p) (nonnegative5740 p)
def d5751 (p : Pattern) : Int := if p 163 then d5604 p else d5743 p
theorem agree5751 (p q : Pattern) (h : Agree support p q) : d5751 p = d5751 q := by
  simp only [d5751, h 163 (by decide), agree5604 p q h, agree5743 p q h]
theorem nonnegative5751 (p : Pattern) : 0 ≤ d5751 p :=
  nonnegative_ite (p 163) (nonnegative5604 p) (nonnegative5743 p)
def d5752 (p : Pattern) : Int := if p 162 then d5751 p else d5750 p
theorem agree5752 (p q : Pattern) (h : Agree support p q) : d5752 p = d5752 q := by
  simp only [d5752, h 162 (by decide), agree5751 p q h, agree5750 p q h]
theorem nonnegative5752 (p : Pattern) : 0 ≤ d5752 p :=
  nonnegative_ite (p 162) (nonnegative5751 p) (nonnegative5750 p)
def d5753 (p : Pattern) : Int := if p 163 then d12 p else d5743 p
theorem agree5753 (p q : Pattern) (h : Agree support p q) : d5753 p = d5753 q := by
  simp only [d5753, h 163 (by decide), agree12 p q h, agree5743 p q h]
theorem nonnegative5753 (p : Pattern) : 0 ≤ d5753 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5743 p)
def d5754 (p : Pattern) : Int := if p 162 then d12 p else d5753 p
theorem agree5754 (p q : Pattern) (h : Agree support p q) : d5754 p = d5754 q := by
  simp only [d5754, h 162 (by decide), agree12 p q h, agree5753 p q h]
theorem nonnegative5754 (p : Pattern) : 0 ≤ d5754 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5753 p)
def d5755 (p : Pattern) : Int := if p 161 then d5754 p else d5752 p
theorem agree5755 (p q : Pattern) (h : Agree support p q) : d5755 p = d5755 q := by
  simp only [d5755, h 161 (by decide), agree5754 p q h, agree5752 p q h]
theorem nonnegative5755 (p : Pattern) : 0 ≤ d5755 p :=
  nonnegative_ite (p 161) (nonnegative5754 p) (nonnegative5752 p)
def d5756 (p : Pattern) : Int := if p 160 then d5755 p else d5633 p
theorem agree5756 (p q : Pattern) (h : Agree support p q) : d5756 p = d5756 q := by
  simp only [d5756, h 160 (by decide), agree5755 p q h, agree5633 p q h]
theorem nonnegative5756 (p : Pattern) : 0 ≤ d5756 p :=
  nonnegative_ite (p 160) (nonnegative5755 p) (nonnegative5633 p)
def d5757 (p : Pattern) : Int := if p 141 then d5756 p else d5749 p
theorem agree5757 (p q : Pattern) (h : Agree support p q) : d5757 p = d5757 q := by
  simp only [d5757, h 141 (by decide), agree5756 p q h, agree5749 p q h]
theorem nonnegative5757 (p : Pattern) : 0 ≤ d5757 p :=
  nonnegative_ite (p 141) (nonnegative5756 p) (nonnegative5749 p)
def d5758 (p : Pattern) : Int := if p 162 then d5624 p else d5611 p
theorem agree5758 (p q : Pattern) (h : Agree support p q) : d5758 p = d5758 q := by
  simp only [d5758, h 162 (by decide), agree5624 p q h, agree5611 p q h]
theorem nonnegative5758 (p : Pattern) : 0 ≤ d5758 p :=
  nonnegative_ite (p 162) (nonnegative5624 p) (nonnegative5611 p)
def d5759 (p : Pattern) : Int := if p 161 then d5625 p else d5758 p
theorem agree5759 (p q : Pattern) (h : Agree support p q) : d5759 p = d5759 q := by
  simp only [d5759, h 161 (by decide), agree5625 p q h, agree5758 p q h]
theorem nonnegative5759 (p : Pattern) : 0 ≤ d5759 p :=
  nonnegative_ite (p 161) (nonnegative5625 p) (nonnegative5758 p)
end NetHack.Sokoban22Refined85
