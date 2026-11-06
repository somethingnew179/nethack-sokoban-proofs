/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes47
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d5760 (p : Pattern) : Int := if p 224 then d315 p else d191 p
theorem agree5760 (p q : Pattern) (h : Agree support p q) : d5760 p = d5760 q := by
  simp only [d5760, h 224 (by decide), agree315 p q h, agree191 p q h]
theorem nonnegative5760 (p : Pattern) : 0 ≤ d5760 p :=
  nonnegative_ite (p 224) (nonnegative315 p) (nonnegative191 p)
def d5761 (p : Pattern) : Int := if p 204 then d5760 p else d191 p
theorem agree5761 (p q : Pattern) (h : Agree support p q) : d5761 p = d5761 q := by
  simp only [d5761, h 204 (by decide), agree5760 p q h, agree191 p q h]
theorem nonnegative5761 (p : Pattern) : 0 ≤ d5761 p :=
  nonnegative_ite (p 204) (nonnegative5760 p) (nonnegative191 p)
def d5762 (p : Pattern) : Int := if p 204 then d12 p else d5760 p
theorem agree5762 (p q : Pattern) (h : Agree support p q) : d5762 p = d5762 q := by
  simp only [d5762, h 204 (by decide), agree12 p q h, agree5760 p q h]
theorem nonnegative5762 (p : Pattern) : 0 ≤ d5762 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5760 p)
def d5763 (p : Pattern) : Int := if p 182 then d5762 p else d5761 p
theorem agree5763 (p q : Pattern) (h : Agree support p q) : d5763 p = d5763 q := by
  simp only [d5763, h 182 (by decide), agree5762 p q h, agree5761 p q h]
theorem nonnegative5763 (p : Pattern) : 0 ≤ d5763 p :=
  nonnegative_ite (p 182) (nonnegative5762 p) (nonnegative5761 p)
def d5764 (p : Pattern) : Int := if p 163 then d5763 p else d5613 p
theorem agree5764 (p q : Pattern) (h : Agree support p q) : d5764 p = d5764 q := by
  simp only [d5764, h 163 (by decide), agree5763 p q h, agree5613 p q h]
theorem nonnegative5764 (p : Pattern) : 0 ≤ d5764 p :=
  nonnegative_ite (p 163) (nonnegative5763 p) (nonnegative5613 p)
def d5765 (p : Pattern) : Int := if p 162 then d12 p else d5764 p
theorem agree5765 (p q : Pattern) (h : Agree support p q) : d5765 p = d5765 q := by
  simp only [d5765, h 162 (by decide), agree12 p q h, agree5764 p q h]
theorem nonnegative5765 (p : Pattern) : 0 ≤ d5765 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5764 p)
def d5766 (p : Pattern) : Int := if p 161 then d12 p else d5765 p
theorem agree5766 (p q : Pattern) (h : Agree support p q) : d5766 p = d5766 q := by
  simp only [d5766, h 161 (by decide), agree12 p q h, agree5765 p q h]
theorem nonnegative5766 (p : Pattern) : 0 ≤ d5766 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5765 p)
def d5767 (p : Pattern) : Int := if p 160 then d5766 p else d5759 p
theorem agree5767 (p q : Pattern) (h : Agree support p q) : d5767 p = d5767 q := by
  simp only [d5767, h 160 (by decide), agree5766 p q h, agree5759 p q h]
theorem nonnegative5767 (p : Pattern) : 0 ≤ d5767 p :=
  nonnegative_ite (p 160) (nonnegative5766 p) (nonnegative5759 p)
def d5768 (p : Pattern) : Int := if p 163 then d5594 p else d5613 p
theorem agree5768 (p q : Pattern) (h : Agree support p q) : d5768 p = d5768 q := by
  simp only [d5768, h 163 (by decide), agree5594 p q h, agree5613 p q h]
theorem nonnegative5768 (p : Pattern) : 0 ≤ d5768 p :=
  nonnegative_ite (p 163) (nonnegative5594 p) (nonnegative5613 p)
def d5769 (p : Pattern) : Int := if p 162 then d5768 p else d5621 p
theorem agree5769 (p q : Pattern) (h : Agree support p q) : d5769 p = d5769 q := by
  simp only [d5769, h 162 (by decide), agree5768 p q h, agree5621 p q h]
theorem nonnegative5769 (p : Pattern) : 0 ≤ d5769 p :=
  nonnegative_ite (p 162) (nonnegative5768 p) (nonnegative5621 p)
def d5770 (p : Pattern) : Int := if p 161 then d5635 p else d5769 p
theorem agree5770 (p q : Pattern) (h : Agree support p q) : d5770 p = d5770 q := by
  simp only [d5770, h 161 (by decide), agree5635 p q h, agree5769 p q h]
theorem nonnegative5770 (p : Pattern) : 0 ≤ d5770 p :=
  nonnegative_ite (p 161) (nonnegative5635 p) (nonnegative5769 p)
def d5771 (p : Pattern) : Int := if p 163 then d12 p else d5763 p
theorem agree5771 (p q : Pattern) (h : Agree support p q) : d5771 p = d5771 q := by
  simp only [d5771, h 163 (by decide), agree12 p q h, agree5763 p q h]
theorem nonnegative5771 (p : Pattern) : 0 ≤ d5771 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5763 p)
def d5772 (p : Pattern) : Int := if p 162 then d12 p else d5771 p
theorem agree5772 (p q : Pattern) (h : Agree support p q) : d5772 p = d5772 q := by
  simp only [d5772, h 162 (by decide), agree12 p q h, agree5771 p q h]
theorem nonnegative5772 (p : Pattern) : 0 ≤ d5772 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5771 p)
def d5773 (p : Pattern) : Int := if p 161 then d12 p else d5772 p
theorem agree5773 (p q : Pattern) (h : Agree support p q) : d5773 p = d5773 q := by
  simp only [d5773, h 161 (by decide), agree12 p q h, agree5772 p q h]
theorem nonnegative5773 (p : Pattern) : 0 ≤ d5773 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5772 p)
def d5774 (p : Pattern) : Int := if p 160 then d5773 p else d5770 p
theorem agree5774 (p q : Pattern) (h : Agree support p q) : d5774 p = d5774 q := by
  simp only [d5774, h 160 (by decide), agree5773 p q h, agree5770 p q h]
theorem nonnegative5774 (p : Pattern) : 0 ≤ d5774 p :=
  nonnegative_ite (p 160) (nonnegative5773 p) (nonnegative5770 p)
def d5775 (p : Pattern) : Int := if p 141 then d5774 p else d5767 p
theorem agree5775 (p q : Pattern) (h : Agree support p q) : d5775 p = d5775 q := by
  simp only [d5775, h 141 (by decide), agree5774 p q h, agree5767 p q h]
theorem nonnegative5775 (p : Pattern) : 0 ≤ d5775 p :=
  nonnegative_ite (p 141) (nonnegative5774 p) (nonnegative5767 p)
def d5776 (p : Pattern) : Int := if p 138 then d5775 p else d5757 p
theorem agree5776 (p q : Pattern) (h : Agree support p q) : d5776 p = d5776 q := by
  simp only [d5776, h 138 (by decide), agree5775 p q h, agree5757 p q h]
theorem nonnegative5776 (p : Pattern) : 0 ≤ d5776 p :=
  nonnegative_ite (p 138) (nonnegative5775 p) (nonnegative5757 p)
def d5777 (p : Pattern) : Int := if p 138 then d12 p else d5775 p
theorem agree5777 (p q : Pattern) (h : Agree support p q) : d5777 p = d5777 q := by
  simp only [d5777, h 138 (by decide), agree12 p q h, agree5775 p q h]
theorem nonnegative5777 (p : Pattern) : 0 ≤ d5777 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5775 p)
def d5778 (p : Pattern) : Int := if p 116 then d5777 p else d5776 p
theorem agree5778 (p q : Pattern) (h : Agree support p q) : d5778 p = d5778 q := by
  simp only [d5778, h 116 (by decide), agree5777 p q h, agree5776 p q h]
theorem nonnegative5778 (p : Pattern) : 0 ≤ d5778 p :=
  nonnegative_ite (p 116) (nonnegative5777 p) (nonnegative5776 p)
def d5779 (p : Pattern) : Int := if p 115 then d5778 p else d5649 p
theorem agree5779 (p q : Pattern) (h : Agree support p q) : d5779 p = d5779 q := by
  simp only [d5779, h 115 (by decide), agree5778 p q h, agree5649 p q h]
theorem nonnegative5779 (p : Pattern) : 0 ≤ d5779 p :=
  nonnegative_ite (p 115) (nonnegative5778 p) (nonnegative5649 p)
def d5780 (p : Pattern) : Int := if p 71 then d5779 p else d5652 p
theorem agree5780 (p q : Pattern) (h : Agree support p q) : d5780 p = d5780 q := by
  simp only [d5780, h 71 (by decide), agree5779 p q h, agree5652 p q h]
theorem nonnegative5780 (p : Pattern) : 0 ≤ d5780 p :=
  nonnegative_ite (p 71) (nonnegative5779 p) (nonnegative5652 p)
def d5781 (p : Pattern) : Int := if p 163 then d12 p else d5662 p
theorem agree5781 (p q : Pattern) (h : Agree support p q) : d5781 p = d5781 q := by
  simp only [d5781, h 163 (by decide), agree12 p q h, agree5662 p q h]
theorem nonnegative5781 (p : Pattern) : 0 ≤ d5781 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5662 p)
def d5782 (p : Pattern) : Int := if p 162 then d5781 p else d5687 p
theorem agree5782 (p q : Pattern) (h : Agree support p q) : d5782 p = d5782 q := by
  simp only [d5782, h 162 (by decide), agree5781 p q h, agree5687 p q h]
theorem nonnegative5782 (p : Pattern) : 0 ≤ d5782 p :=
  nonnegative_ite (p 162) (nonnegative5781 p) (nonnegative5687 p)
def d5783 (p : Pattern) : Int := if p 162 then d12 p else d5781 p
theorem agree5783 (p q : Pattern) (h : Agree support p q) : d5783 p = d5783 q := by
  simp only [d5783, h 162 (by decide), agree12 p q h, agree5781 p q h]
theorem nonnegative5783 (p : Pattern) : 0 ≤ d5783 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5781 p)
def d5784 (p : Pattern) : Int := if p 161 then d5783 p else d5782 p
theorem agree5784 (p q : Pattern) (h : Agree support p q) : d5784 p = d5784 q := by
  simp only [d5784, h 161 (by decide), agree5783 p q h, agree5782 p q h]
theorem nonnegative5784 (p : Pattern) : 0 ≤ d5784 p :=
  nonnegative_ite (p 161) (nonnegative5783 p) (nonnegative5782 p)
def d5785 (p : Pattern) : Int := if p 163 then d12 p else d5676 p
theorem agree5785 (p q : Pattern) (h : Agree support p q) : d5785 p = d5785 q := by
  simp only [d5785, h 163 (by decide), agree12 p q h, agree5676 p q h]
theorem nonnegative5785 (p : Pattern) : 0 ≤ d5785 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5676 p)
def d5786 (p : Pattern) : Int := if p 162 then d5785 p else d5694 p
theorem agree5786 (p q : Pattern) (h : Agree support p q) : d5786 p = d5786 q := by
  simp only [d5786, h 162 (by decide), agree5785 p q h, agree5694 p q h]
theorem nonnegative5786 (p : Pattern) : 0 ≤ d5786 p :=
  nonnegative_ite (p 162) (nonnegative5785 p) (nonnegative5694 p)
def d5787 (p : Pattern) : Int := if p 162 then d12 p else d5785 p
theorem agree5787 (p q : Pattern) (h : Agree support p q) : d5787 p = d5787 q := by
  simp only [d5787, h 162 (by decide), agree12 p q h, agree5785 p q h]
theorem nonnegative5787 (p : Pattern) : 0 ≤ d5787 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5785 p)
def d5788 (p : Pattern) : Int := if p 161 then d5787 p else d5786 p
theorem agree5788 (p q : Pattern) (h : Agree support p q) : d5788 p = d5788 q := by
  simp only [d5788, h 161 (by decide), agree5787 p q h, agree5786 p q h]
theorem nonnegative5788 (p : Pattern) : 0 ≤ d5788 p :=
  nonnegative_ite (p 161) (nonnegative5787 p) (nonnegative5786 p)
def d5789 (p : Pattern) : Int := if p 160 then d5788 p else d5784 p
theorem agree5789 (p q : Pattern) (h : Agree support p q) : d5789 p = d5789 q := by
  simp only [d5789, h 160 (by decide), agree5788 p q h, agree5784 p q h]
theorem nonnegative5789 (p : Pattern) : 0 ≤ d5789 p :=
  nonnegative_ite (p 160) (nonnegative5788 p) (nonnegative5784 p)
def d5790 (p : Pattern) : Int := if p 141 then d5789 p else d5682 p
theorem agree5790 (p q : Pattern) (h : Agree support p q) : d5790 p = d5790 q := by
  simp only [d5790, h 141 (by decide), agree5789 p q h, agree5682 p q h]
theorem nonnegative5790 (p : Pattern) : 0 ≤ d5790 p :=
  nonnegative_ite (p 141) (nonnegative5789 p) (nonnegative5682 p)
def d5791 (p : Pattern) : Int := if p 163 then d12 p else d5705 p
theorem agree5791 (p q : Pattern) (h : Agree support p q) : d5791 p = d5791 q := by
  simp only [d5791, h 163 (by decide), agree12 p q h, agree5705 p q h]
theorem nonnegative5791 (p : Pattern) : 0 ≤ d5791 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5705 p)
def d5792 (p : Pattern) : Int := if p 162 then d5791 p else d5717 p
theorem agree5792 (p q : Pattern) (h : Agree support p q) : d5792 p = d5792 q := by
  simp only [d5792, h 162 (by decide), agree5791 p q h, agree5717 p q h]
theorem nonnegative5792 (p : Pattern) : 0 ≤ d5792 p :=
  nonnegative_ite (p 162) (nonnegative5791 p) (nonnegative5717 p)
def d5793 (p : Pattern) : Int := if p 162 then d12 p else d5791 p
theorem agree5793 (p q : Pattern) (h : Agree support p q) : d5793 p = d5793 q := by
  simp only [d5793, h 162 (by decide), agree12 p q h, agree5791 p q h]
theorem nonnegative5793 (p : Pattern) : 0 ≤ d5793 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5791 p)
def d5794 (p : Pattern) : Int := if p 161 then d5793 p else d5792 p
theorem agree5794 (p q : Pattern) (h : Agree support p q) : d5794 p = d5794 q := by
  simp only [d5794, h 161 (by decide), agree5793 p q h, agree5792 p q h]
theorem nonnegative5794 (p : Pattern) : 0 ≤ d5794 p :=
  nonnegative_ite (p 161) (nonnegative5793 p) (nonnegative5792 p)
def d5795 (p : Pattern) : Int := if p 160 then d5725 p else d5794 p
theorem agree5795 (p q : Pattern) (h : Agree support p q) : d5795 p = d5795 q := by
  simp only [d5795, h 160 (by decide), agree5725 p q h, agree5794 p q h]
theorem nonnegative5795 (p : Pattern) : 0 ≤ d5795 p :=
  nonnegative_ite (p 160) (nonnegative5725 p) (nonnegative5794 p)
def d5796 (p : Pattern) : Int := if p 141 then d5795 p else d5716 p
theorem agree5796 (p q : Pattern) (h : Agree support p q) : d5796 p = d5796 q := by
  simp only [d5796, h 141 (by decide), agree5795 p q h, agree5716 p q h]
theorem nonnegative5796 (p : Pattern) : 0 ≤ d5796 p :=
  nonnegative_ite (p 141) (nonnegative5795 p) (nonnegative5716 p)
def d5797 (p : Pattern) : Int := if p 138 then d5796 p else d5790 p
theorem agree5797 (p q : Pattern) (h : Agree support p q) : d5797 p = d5797 q := by
  simp only [d5797, h 138 (by decide), agree5796 p q h, agree5790 p q h]
theorem nonnegative5797 (p : Pattern) : 0 ≤ d5797 p :=
  nonnegative_ite (p 138) (nonnegative5796 p) (nonnegative5790 p)
def d5798 (p : Pattern) : Int := if p 138 then d5732 p else d5796 p
theorem agree5798 (p q : Pattern) (h : Agree support p q) : d5798 p = d5798 q := by
  simp only [d5798, h 138 (by decide), agree5732 p q h, agree5796 p q h]
theorem nonnegative5798 (p : Pattern) : 0 ≤ d5798 p :=
  nonnegative_ite (p 138) (nonnegative5732 p) (nonnegative5796 p)
def d5799 (p : Pattern) : Int := if p 116 then d5798 p else d5797 p
theorem agree5799 (p q : Pattern) (h : Agree support p q) : d5799 p = d5799 q := by
  simp only [d5799, h 116 (by decide), agree5798 p q h, agree5797 p q h]
theorem nonnegative5799 (p : Pattern) : 0 ≤ d5799 p :=
  nonnegative_ite (p 116) (nonnegative5798 p) (nonnegative5797 p)
def d5800 (p : Pattern) : Int := if p 182 then d5672 p else d5683 p
theorem agree5800 (p q : Pattern) (h : Agree support p q) : d5800 p = d5800 q := by
  simp only [d5800, h 182 (by decide), agree5672 p q h, agree5683 p q h]
theorem nonnegative5800 (p : Pattern) : 0 ≤ d5800 p :=
  nonnegative_ite (p 182) (nonnegative5672 p) (nonnegative5683 p)
def d5801 (p : Pattern) : Int := if p 163 then d5800 p else d5710 p
theorem agree5801 (p q : Pattern) (h : Agree support p q) : d5801 p = d5801 q := by
  simp only [d5801, h 163 (by decide), agree5800 p q h, agree5710 p q h]
theorem nonnegative5801 (p : Pattern) : 0 ≤ d5801 p :=
  nonnegative_ite (p 163) (nonnegative5800 p) (nonnegative5710 p)
def d5802 (p : Pattern) : Int := if p 162 then d5785 p else d5801 p
theorem agree5802 (p q : Pattern) (h : Agree support p q) : d5802 p = d5802 q := by
  simp only [d5802, h 162 (by decide), agree5785 p q h, agree5801 p q h]
theorem nonnegative5802 (p : Pattern) : 0 ≤ d5802 p :=
  nonnegative_ite (p 162) (nonnegative5785 p) (nonnegative5801 p)
def d5803 (p : Pattern) : Int := if p 182 then d12 p else d5711 p
theorem agree5803 (p q : Pattern) (h : Agree support p q) : d5803 p = d5803 q := by
  simp only [d5803, h 182 (by decide), agree12 p q h, agree5711 p q h]
theorem nonnegative5803 (p : Pattern) : 0 ≤ d5803 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5711 p)
def d5804 (p : Pattern) : Int := if p 163 then d12 p else d5803 p
theorem agree5804 (p q : Pattern) (h : Agree support p q) : d5804 p = d5804 q := by
  simp only [d5804, h 163 (by decide), agree12 p q h, agree5803 p q h]
theorem nonnegative5804 (p : Pattern) : 0 ≤ d5804 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5803 p)
def d5805 (p : Pattern) : Int := if p 162 then d12 p else d5804 p
theorem agree5805 (p q : Pattern) (h : Agree support p q) : d5805 p = d5805 q := by
  simp only [d5805, h 162 (by decide), agree12 p q h, agree5804 p q h]
theorem nonnegative5805 (p : Pattern) : 0 ≤ d5805 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5804 p)
def d5806 (p : Pattern) : Int := if p 161 then d5805 p else d5802 p
theorem agree5806 (p q : Pattern) (h : Agree support p q) : d5806 p = d5806 q := by
  simp only [d5806, h 161 (by decide), agree5805 p q h, agree5802 p q h]
theorem nonnegative5806 (p : Pattern) : 0 ≤ d5806 p :=
  nonnegative_ite (p 161) (nonnegative5805 p) (nonnegative5802 p)
def d5807 (p : Pattern) : Int := if p 160 then d5806 p else d5709 p
theorem agree5807 (p q : Pattern) (h : Agree support p q) : d5807 p = d5807 q := by
  simp only [d5807, h 160 (by decide), agree5806 p q h, agree5709 p q h]
theorem nonnegative5807 (p : Pattern) : 0 ≤ d5807 p :=
  nonnegative_ite (p 160) (nonnegative5806 p) (nonnegative5709 p)
def d5808 (p : Pattern) : Int := if p 182 then d5672 p else d5659 p
theorem agree5808 (p q : Pattern) (h : Agree support p q) : d5808 p = d5808 q := by
  simp only [d5808, h 182 (by decide), agree5672 p q h, agree5659 p q h]
theorem nonnegative5808 (p : Pattern) : 0 ≤ d5808 p :=
  nonnegative_ite (p 182) (nonnegative5672 p) (nonnegative5659 p)
def d5809 (p : Pattern) : Int := if p 163 then d5676 p else d5808 p
theorem agree5809 (p q : Pattern) (h : Agree support p q) : d5809 p = d5809 q := by
  simp only [d5809, h 163 (by decide), agree5676 p q h, agree5808 p q h]
theorem nonnegative5809 (p : Pattern) : 0 ≤ d5809 p :=
  nonnegative_ite (p 163) (nonnegative5676 p) (nonnegative5808 p)
def d5810 (p : Pattern) : Int := if p 162 then d5804 p else d5809 p
theorem agree5810 (p q : Pattern) (h : Agree support p q) : d5810 p = d5810 q := by
  simp only [d5810, h 162 (by decide), agree5804 p q h, agree5809 p q h]
theorem nonnegative5810 (p : Pattern) : 0 ≤ d5810 p :=
  nonnegative_ite (p 162) (nonnegative5804 p) (nonnegative5809 p)
def d5811 (p : Pattern) : Int := if p 162 then d12 p else d5577 p
theorem agree5811 (p q : Pattern) (h : Agree support p q) : d5811 p = d5811 q := by
  simp only [d5811, h 162 (by decide), agree12 p q h, agree5577 p q h]
theorem nonnegative5811 (p : Pattern) : 0 ≤ d5811 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5577 p)
def d5812 (p : Pattern) : Int := if p 161 then d5811 p else d5810 p
theorem agree5812 (p q : Pattern) (h : Agree support p q) : d5812 p = d5812 q := by
  simp only [d5812, h 161 (by decide), agree5811 p q h, agree5810 p q h]
theorem nonnegative5812 (p : Pattern) : 0 ≤ d5812 p :=
  nonnegative_ite (p 161) (nonnegative5811 p) (nonnegative5810 p)
def d5813 (p : Pattern) : Int := if p 160 then d5812 p else d5794 p
theorem agree5813 (p q : Pattern) (h : Agree support p q) : d5813 p = d5813 q := by
  simp only [d5813, h 160 (by decide), agree5812 p q h, agree5794 p q h]
theorem nonnegative5813 (p : Pattern) : 0 ≤ d5813 p :=
  nonnegative_ite (p 160) (nonnegative5812 p) (nonnegative5794 p)
def d5814 (p : Pattern) : Int := if p 141 then d5813 p else d5807 p
theorem agree5814 (p q : Pattern) (h : Agree support p q) : d5814 p = d5814 q := by
  simp only [d5814, h 141 (by decide), agree5813 p q h, agree5807 p q h]
theorem nonnegative5814 (p : Pattern) : 0 ≤ d5814 p :=
  nonnegative_ite (p 141) (nonnegative5813 p) (nonnegative5807 p)
def d5815 (p : Pattern) : Int := if p 163 then d5594 p else d5710 p
theorem agree5815 (p q : Pattern) (h : Agree support p q) : d5815 p = d5815 q := by
  simp only [d5815, h 163 (by decide), agree5594 p q h, agree5710 p q h]
theorem nonnegative5815 (p : Pattern) : 0 ≤ d5815 p :=
  nonnegative_ite (p 163) (nonnegative5594 p) (nonnegative5710 p)
def d5816 (p : Pattern) : Int := if p 162 then d5815 p else d5703 p
theorem agree5816 (p q : Pattern) (h : Agree support p q) : d5816 p = d5816 q := by
  simp only [d5816, h 162 (by decide), agree5815 p q h, agree5703 p q h]
theorem nonnegative5816 (p : Pattern) : 0 ≤ d5816 p :=
  nonnegative_ite (p 162) (nonnegative5815 p) (nonnegative5703 p)
def d5817 (p : Pattern) : Int := if p 161 then d5721 p else d5816 p
theorem agree5817 (p q : Pattern) (h : Agree support p q) : d5817 p = d5817 q := by
  simp only [d5817, h 161 (by decide), agree5721 p q h, agree5816 p q h]
theorem nonnegative5817 (p : Pattern) : 0 ≤ d5817 p :=
  nonnegative_ite (p 161) (nonnegative5721 p) (nonnegative5816 p)
def d5818 (p : Pattern) : Int := if p 160 then d5725 p else d5817 p
theorem agree5818 (p q : Pattern) (h : Agree support p q) : d5818 p = d5818 q := by
  simp only [d5818, h 160 (by decide), agree5725 p q h, agree5817 p q h]
theorem nonnegative5818 (p : Pattern) : 0 ≤ d5818 p :=
  nonnegative_ite (p 160) (nonnegative5725 p) (nonnegative5817 p)
def d5819 (p : Pattern) : Int := if p 162 then d5791 p else d5710 p
theorem agree5819 (p q : Pattern) (h : Agree support p q) : d5819 p = d5819 q := by
  simp only [d5819, h 162 (by decide), agree5791 p q h, agree5710 p q h]
theorem nonnegative5819 (p : Pattern) : 0 ≤ d5819 p :=
  nonnegative_ite (p 162) (nonnegative5791 p) (nonnegative5710 p)
def d5820 (p : Pattern) : Int := if p 161 then d5724 p else d5819 p
theorem agree5820 (p q : Pattern) (h : Agree support p q) : d5820 p = d5820 q := by
  simp only [d5820, h 161 (by decide), agree5724 p q h, agree5819 p q h]
theorem nonnegative5820 (p : Pattern) : 0 ≤ d5820 p :=
  nonnegative_ite (p 161) (nonnegative5724 p) (nonnegative5819 p)
def d5821 (p : Pattern) : Int := if p 162 then d12 p else d5618 p
theorem agree5821 (p q : Pattern) (h : Agree support p q) : d5821 p = d5821 q := by
  simp only [d5821, h 162 (by decide), agree12 p q h, agree5618 p q h]
theorem nonnegative5821 (p : Pattern) : 0 ≤ d5821 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5618 p)
def d5822 (p : Pattern) : Int := if p 161 then d12 p else d5821 p
theorem agree5822 (p q : Pattern) (h : Agree support p q) : d5822 p = d5822 q := by
  simp only [d5822, h 161 (by decide), agree12 p q h, agree5821 p q h]
theorem nonnegative5822 (p : Pattern) : 0 ≤ d5822 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5821 p)
def d5823 (p : Pattern) : Int := if p 160 then d5822 p else d5820 p
theorem agree5823 (p q : Pattern) (h : Agree support p q) : d5823 p = d5823 q := by
  simp only [d5823, h 160 (by decide), agree5822 p q h, agree5820 p q h]
theorem nonnegative5823 (p : Pattern) : 0 ≤ d5823 p :=
  nonnegative_ite (p 160) (nonnegative5822 p) (nonnegative5820 p)
def d5824 (p : Pattern) : Int := if p 141 then d5823 p else d5818 p
theorem agree5824 (p q : Pattern) (h : Agree support p q) : d5824 p = d5824 q := by
  simp only [d5824, h 141 (by decide), agree5823 p q h, agree5818 p q h]
theorem nonnegative5824 (p : Pattern) : 0 ≤ d5824 p :=
  nonnegative_ite (p 141) (nonnegative5823 p) (nonnegative5818 p)
def d5825 (p : Pattern) : Int := if p 138 then d5824 p else d5814 p
theorem agree5825 (p q : Pattern) (h : Agree support p q) : d5825 p = d5825 q := by
  simp only [d5825, h 138 (by decide), agree5824 p q h, agree5814 p q h]
theorem nonnegative5825 (p : Pattern) : 0 ≤ d5825 p :=
  nonnegative_ite (p 138) (nonnegative5824 p) (nonnegative5814 p)
def d5826 (p : Pattern) : Int := if p 163 then d5617 p else d5710 p
theorem agree5826 (p q : Pattern) (h : Agree support p q) : d5826 p = d5826 q := by
  simp only [d5826, h 163 (by decide), agree5617 p q h, agree5710 p q h]
theorem nonnegative5826 (p : Pattern) : 0 ≤ d5826 p :=
  nonnegative_ite (p 163) (nonnegative5617 p) (nonnegative5710 p)
def d5827 (p : Pattern) : Int := if p 162 then d5826 p else d5703 p
theorem agree5827 (p q : Pattern) (h : Agree support p q) : d5827 p = d5827 q := by
  simp only [d5827, h 162 (by decide), agree5826 p q h, agree5703 p q h]
theorem nonnegative5827 (p : Pattern) : 0 ≤ d5827 p :=
  nonnegative_ite (p 162) (nonnegative5826 p) (nonnegative5703 p)
def d5828 (p : Pattern) : Int := if p 163 then d5617 p else d5705 p
theorem agree5828 (p q : Pattern) (h : Agree support p q) : d5828 p = d5828 q := by
  simp only [d5828, h 163 (by decide), agree5617 p q h, agree5705 p q h]
theorem nonnegative5828 (p : Pattern) : 0 ≤ d5828 p :=
  nonnegative_ite (p 163) (nonnegative5617 p) (nonnegative5705 p)
def d5829 (p : Pattern) : Int := if p 162 then d12 p else d5828 p
theorem agree5829 (p q : Pattern) (h : Agree support p q) : d5829 p = d5829 q := by
  simp only [d5829, h 162 (by decide), agree12 p q h, agree5828 p q h]
theorem nonnegative5829 (p : Pattern) : 0 ≤ d5829 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5828 p)
def d5830 (p : Pattern) : Int := if p 161 then d5829 p else d5827 p
theorem agree5830 (p q : Pattern) (h : Agree support p q) : d5830 p = d5830 q := by
  simp only [d5830, h 161 (by decide), agree5829 p q h, agree5827 p q h]
theorem nonnegative5830 (p : Pattern) : 0 ≤ d5830 p :=
  nonnegative_ite (p 161) (nonnegative5829 p) (nonnegative5827 p)
def d5831 (p : Pattern) : Int := if p 163 then d5594 p else d5712 p
theorem agree5831 (p q : Pattern) (h : Agree support p q) : d5831 p = d5831 q := by
  simp only [d5831, h 163 (by decide), agree5594 p q h, agree5712 p q h]
theorem nonnegative5831 (p : Pattern) : 0 ≤ d5831 p :=
  nonnegative_ite (p 163) (nonnegative5594 p) (nonnegative5712 p)
def d5832 (p : Pattern) : Int := if p 162 then d12 p else d5831 p
theorem agree5832 (p q : Pattern) (h : Agree support p q) : d5832 p = d5832 q := by
  simp only [d5832, h 162 (by decide), agree12 p q h, agree5831 p q h]
theorem nonnegative5832 (p : Pattern) : 0 ≤ d5832 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5831 p)
def d5833 (p : Pattern) : Int := if p 161 then d12 p else d5832 p
theorem agree5833 (p q : Pattern) (h : Agree support p q) : d5833 p = d5833 q := by
  simp only [d5833, h 161 (by decide), agree12 p q h, agree5832 p q h]
theorem nonnegative5833 (p : Pattern) : 0 ≤ d5833 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5832 p)
def d5834 (p : Pattern) : Int := if p 160 then d5833 p else d5830 p
theorem agree5834 (p q : Pattern) (h : Agree support p q) : d5834 p = d5834 q := by
  simp only [d5834, h 160 (by decide), agree5833 p q h, agree5830 p q h]
theorem nonnegative5834 (p : Pattern) : 0 ≤ d5834 p :=
  nonnegative_ite (p 160) (nonnegative5833 p) (nonnegative5830 p)
def d5835 (p : Pattern) : Int := if p 141 then d5823 p else d5834 p
theorem agree5835 (p q : Pattern) (h : Agree support p q) : d5835 p = d5835 q := by
  simp only [d5835, h 141 (by decide), agree5823 p q h, agree5834 p q h]
theorem nonnegative5835 (p : Pattern) : 0 ≤ d5835 p :=
  nonnegative_ite (p 141) (nonnegative5823 p) (nonnegative5834 p)
def d5836 (p : Pattern) : Int := if p 138 then d12 p else d5835 p
theorem agree5836 (p q : Pattern) (h : Agree support p q) : d5836 p = d5836 q := by
  simp only [d5836, h 138 (by decide), agree12 p q h, agree5835 p q h]
theorem nonnegative5836 (p : Pattern) : 0 ≤ d5836 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5835 p)
def d5837 (p : Pattern) : Int := if p 116 then d5836 p else d5825 p
theorem agree5837 (p q : Pattern) (h : Agree support p q) : d5837 p = d5837 q := by
  simp only [d5837, h 116 (by decide), agree5836 p q h, agree5825 p q h]
theorem nonnegative5837 (p : Pattern) : 0 ≤ d5837 p :=
  nonnegative_ite (p 116) (nonnegative5836 p) (nonnegative5825 p)
def d5838 (p : Pattern) : Int := if p 115 then d5837 p else d5799 p
theorem agree5838 (p q : Pattern) (h : Agree support p q) : d5838 p = d5838 q := by
  simp only [d5838, h 115 (by decide), agree5837 p q h, agree5799 p q h]
theorem nonnegative5838 (p : Pattern) : 0 ≤ d5838 p :=
  nonnegative_ite (p 115) (nonnegative5837 p) (nonnegative5799 p)
def d5839 (p : Pattern) : Int := if p 71 then d5838 p else d5652 p
theorem agree5839 (p q : Pattern) (h : Agree support p q) : d5839 p = d5839 q := by
  simp only [d5839, h 71 (by decide), agree5838 p q h, agree5652 p q h]
theorem nonnegative5839 (p : Pattern) : 0 ≤ d5839 p :=
  nonnegative_ite (p 71) (nonnegative5838 p) (nonnegative5652 p)
def d5840 (p : Pattern) : Int := if p 49 then d5839 p else d5780 p
theorem agree5840 (p q : Pattern) (h : Agree support p q) : d5840 p = d5840 q := by
  simp only [d5840, h 49 (by decide), agree5839 p q h, agree5780 p q h]
theorem nonnegative5840 (p : Pattern) : 0 ≤ d5840 p :=
  nonnegative_ite (p 49) (nonnegative5839 p) (nonnegative5780 p)
def d5841 (p : Pattern) : Int := if p 48 then d5840 p else d5739 p
theorem agree5841 (p q : Pattern) (h : Agree support p q) : d5841 p = d5841 q := by
  simp only [d5841, h 48 (by decide), agree5840 p q h, agree5739 p q h]
theorem nonnegative5841 (p : Pattern) : 0 ≤ d5841 p :=
  nonnegative_ite (p 48) (nonnegative5840 p) (nonnegative5739 p)
def d5842 (p : Pattern) : Int := if p 247 then d1 p else d0 p
theorem agree5842 (p q : Pattern) (h : Agree support p q) : d5842 p = d5842 q := by
  simp only [d5842, h 247 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative5842 (p : Pattern) : 0 ≤ d5842 p :=
  nonnegative_ite (p 247) (nonnegative1 p) (nonnegative0 p)
def d5843 (p : Pattern) : Int := if p 247 then d0 p else d1 p
theorem agree5843 (p q : Pattern) (h : Agree support p q) : d5843 p = d5843 q := by
  simp only [d5843, h 247 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative5843 (p : Pattern) : 0 ≤ d5843 p :=
  nonnegative_ite (p 247) (nonnegative0 p) (nonnegative1 p)
def d5844 (p : Pattern) : Int := if p 224 then d0 p else d5843 p
theorem agree5844 (p q : Pattern) (h : Agree support p q) : d5844 p = d5844 q := by
  simp only [d5844, h 224 (by decide), agree0 p q h, agree5843 p q h]
theorem nonnegative5844 (p : Pattern) : 0 ≤ d5844 p :=
  nonnegative_ite (p 224) (nonnegative0 p) (nonnegative5843 p)
def d5845 (p : Pattern) : Int := if p 225 then d5267 p else d0 p
theorem agree5845 (p q : Pattern) (h : Agree support p q) : d5845 p = d5845 q := by
  simp only [d5845, h 225 (by decide), agree5267 p q h, agree0 p q h]
theorem nonnegative5845 (p : Pattern) : 0 ≤ d5845 p :=
  nonnegative_ite (p 225) (nonnegative5267 p) (nonnegative0 p)
def d5846 (p : Pattern) : Int := if p 225 then d5268 p else d1 p
theorem agree5846 (p q : Pattern) (h : Agree support p q) : d5846 p = d5846 q := by
  simp only [d5846, h 225 (by decide), agree5268 p q h, agree1 p q h]
theorem nonnegative5846 (p : Pattern) : 0 ≤ d5846 p :=
  nonnegative_ite (p 225) (nonnegative5268 p) (nonnegative1 p)
def d5847 (p : Pattern) : Int := if p 246 then d0 p else d5843 p
theorem agree5847 (p q : Pattern) (h : Agree support p q) : d5847 p = d5847 q := by
  simp only [d5847, h 246 (by decide), agree0 p q h, agree5843 p q h]
theorem nonnegative5847 (p : Pattern) : 0 ≤ d5847 p :=
  nonnegative_ite (p 246) (nonnegative0 p) (nonnegative5843 p)
def d5848 (p : Pattern) : Int := if p 225 then d5847 p else d5843 p
theorem agree5848 (p q : Pattern) (h : Agree support p q) : d5848 p = d5848 q := by
  simp only [d5848, h 225 (by decide), agree5847 p q h, agree5843 p q h]
theorem nonnegative5848 (p : Pattern) : 0 ≤ d5848 p :=
  nonnegative_ite (p 225) (nonnegative5847 p) (nonnegative5843 p)
def d5849 (p : Pattern) : Int := if p 224 then d0 p else d5848 p
theorem agree5849 (p q : Pattern) (h : Agree support p q) : d5849 p = d5849 q := by
  simp only [d5849, h 224 (by decide), agree0 p q h, agree5848 p q h]
theorem nonnegative5849 (p : Pattern) : 0 ≤ d5849 p :=
  nonnegative_ite (p 224) (nonnegative0 p) (nonnegative5848 p)
def d5850 (p : Pattern) : Int := if p 225 then d0 p else d5843 p
theorem agree5850 (p q : Pattern) (h : Agree support p q) : d5850 p = d5850 q := by
  simp only [d5850, h 225 (by decide), agree0 p q h, agree5843 p q h]
theorem nonnegative5850 (p : Pattern) : 0 ≤ d5850 p :=
  nonnegative_ite (p 225) (nonnegative0 p) (nonnegative5843 p)
def d5851 (p : Pattern) : Int := if p 225 then d0 p else d5268 p
theorem agree5851 (p q : Pattern) (h : Agree support p q) : d5851 p = d5851 q := by
  simp only [d5851, h 225 (by decide), agree0 p q h, agree5268 p q h]
theorem nonnegative5851 (p : Pattern) : 0 ≤ d5851 p :=
  nonnegative_ite (p 225) (nonnegative0 p) (nonnegative5268 p)
def d5852 (p : Pattern) : Int := if p 224 then d5842 p else d0 p
theorem agree5852 (p q : Pattern) (h : Agree support p q) : d5852 p = d5852 q := by
  simp only [d5852, h 224 (by decide), agree5842 p q h, agree0 p q h]
theorem nonnegative5852 (p : Pattern) : 0 ≤ d5852 p :=
  nonnegative_ite (p 224) (nonnegative5842 p) (nonnegative0 p)
def d5853 (p : Pattern) : Int := if p 224 then d5843 p else d1 p
theorem agree5853 (p q : Pattern) (h : Agree support p q) : d5853 p = d5853 q := by
  simp only [d5853, h 224 (by decide), agree5843 p q h, agree1 p q h]
theorem nonnegative5853 (p : Pattern) : 0 ≤ d5853 p :=
  nonnegative_ite (p 224) (nonnegative5843 p) (nonnegative1 p)
def d5854 (p : Pattern) : Int := if p 225 then d0 p else d5847 p
theorem agree5854 (p q : Pattern) (h : Agree support p q) : d5854 p = d5854 q := by
  simp only [d5854, h 225 (by decide), agree0 p q h, agree5847 p q h]
theorem nonnegative5854 (p : Pattern) : 0 ≤ d5854 p :=
  nonnegative_ite (p 225) (nonnegative0 p) (nonnegative5847 p)
def d5855 (p : Pattern) : Int := if p 224 then d5854 p else d5851 p
theorem agree5855 (p q : Pattern) (h : Agree support p q) : d5855 p = d5855 q := by
  simp only [d5855, h 224 (by decide), agree5854 p q h, agree5851 p q h]
theorem nonnegative5855 (p : Pattern) : 0 ≤ d5855 p :=
  nonnegative_ite (p 224) (nonnegative5854 p) (nonnegative5851 p)
def d5856 (p : Pattern) : Int := if p 163 then d1696 p else d1686 p
theorem agree5856 (p q : Pattern) (h : Agree support p q) : d5856 p = d5856 q := by
  simp only [d5856, h 163 (by decide), agree1696 p q h, agree1686 p q h]
theorem nonnegative5856 (p : Pattern) : 0 ≤ d5856 p :=
  nonnegative_ite (p 163) (nonnegative1696 p) (nonnegative1686 p)
def d5857 (p : Pattern) : Int := if p 162 then d5856 p else d1686 p
theorem agree5857 (p q : Pattern) (h : Agree support p q) : d5857 p = d5857 q := by
  simp only [d5857, h 162 (by decide), agree5856 p q h, agree1686 p q h]
theorem nonnegative5857 (p : Pattern) : 0 ≤ d5857 p :=
  nonnegative_ite (p 162) (nonnegative5856 p) (nonnegative1686 p)
def d5858 (p : Pattern) : Int := if p 163 then d12 p else d1704 p
theorem agree5858 (p q : Pattern) (h : Agree support p q) : d5858 p = d5858 q := by
  simp only [d5858, h 163 (by decide), agree12 p q h, agree1704 p q h]
theorem nonnegative5858 (p : Pattern) : 0 ≤ d5858 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1704 p)
def d5859 (p : Pattern) : Int := if p 162 then d5858 p else d5856 p
theorem agree5859 (p q : Pattern) (h : Agree support p q) : d5859 p = d5859 q := by
  simp only [d5859, h 162 (by decide), agree5858 p q h, agree5856 p q h]
theorem nonnegative5859 (p : Pattern) : 0 ≤ d5859 p :=
  nonnegative_ite (p 162) (nonnegative5858 p) (nonnegative5856 p)
def d5860 (p : Pattern) : Int := if p 161 then d5859 p else d5857 p
theorem agree5860 (p q : Pattern) (h : Agree support p q) : d5860 p = d5860 q := by
  simp only [d5860, h 161 (by decide), agree5859 p q h, agree5857 p q h]
theorem nonnegative5860 (p : Pattern) : 0 ≤ d5860 p :=
  nonnegative_ite (p 161) (nonnegative5859 p) (nonnegative5857 p)
def d5861 (p : Pattern) : Int := if p 163 then d1724 p else d1717 p
theorem agree5861 (p q : Pattern) (h : Agree support p q) : d5861 p = d5861 q := by
  simp only [d5861, h 163 (by decide), agree1724 p q h, agree1717 p q h]
theorem nonnegative5861 (p : Pattern) : 0 ≤ d5861 p :=
  nonnegative_ite (p 163) (nonnegative1724 p) (nonnegative1717 p)
def d5862 (p : Pattern) : Int := if p 163 then d12 p else d1729 p
theorem agree5862 (p q : Pattern) (h : Agree support p q) : d5862 p = d5862 q := by
  simp only [d5862, h 163 (by decide), agree12 p q h, agree1729 p q h]
theorem nonnegative5862 (p : Pattern) : 0 ≤ d5862 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1729 p)
def d5863 (p : Pattern) : Int := if p 162 then d5862 p else d5861 p
theorem agree5863 (p q : Pattern) (h : Agree support p q) : d5863 p = d5863 q := by
  simp only [d5863, h 162 (by decide), agree5862 p q h, agree5861 p q h]
theorem nonnegative5863 (p : Pattern) : 0 ≤ d5863 p :=
  nonnegative_ite (p 162) (nonnegative5862 p) (nonnegative5861 p)
def d5864 (p : Pattern) : Int := if p 161 then d12 p else d5863 p
theorem agree5864 (p q : Pattern) (h : Agree support p q) : d5864 p = d5864 q := by
  simp only [d5864, h 161 (by decide), agree12 p q h, agree5863 p q h]
theorem nonnegative5864 (p : Pattern) : 0 ≤ d5864 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5863 p)
def d5865 (p : Pattern) : Int := if p 160 then d5864 p else d5860 p
theorem agree5865 (p q : Pattern) (h : Agree support p q) : d5865 p = d5865 q := by
  simp only [d5865, h 160 (by decide), agree5864 p q h, agree5860 p q h]
theorem nonnegative5865 (p : Pattern) : 0 ≤ d5865 p :=
  nonnegative_ite (p 160) (nonnegative5864 p) (nonnegative5860 p)
def d5866 (p : Pattern) : Int := if p 163 then d1745 p else d1686 p
theorem agree5866 (p q : Pattern) (h : Agree support p q) : d5866 p = d5866 q := by
  simp only [d5866, h 163 (by decide), agree1745 p q h, agree1686 p q h]
theorem nonnegative5866 (p : Pattern) : 0 ≤ d5866 p :=
  nonnegative_ite (p 163) (nonnegative1745 p) (nonnegative1686 p)
def d5867 (p : Pattern) : Int := if p 163 then d1704 p else d1696 p
theorem agree5867 (p q : Pattern) (h : Agree support p q) : d5867 p = d5867 q := by
  simp only [d5867, h 163 (by decide), agree1704 p q h, agree1696 p q h]
theorem nonnegative5867 (p : Pattern) : 0 ≤ d5867 p :=
  nonnegative_ite (p 163) (nonnegative1704 p) (nonnegative1696 p)
def d5868 (p : Pattern) : Int := if p 162 then d5867 p else d5866 p
theorem agree5868 (p q : Pattern) (h : Agree support p q) : d5868 p = d5868 q := by
  simp only [d5868, h 162 (by decide), agree5867 p q h, agree5866 p q h]
theorem nonnegative5868 (p : Pattern) : 0 ≤ d5868 p :=
  nonnegative_ite (p 162) (nonnegative5867 p) (nonnegative5866 p)
def d5869 (p : Pattern) : Int := if p 163 then d1752 p else d1696 p
theorem agree5869 (p q : Pattern) (h : Agree support p q) : d5869 p = d5869 q := by
  simp only [d5869, h 163 (by decide), agree1752 p q h, agree1696 p q h]
theorem nonnegative5869 (p : Pattern) : 0 ≤ d5869 p :=
  nonnegative_ite (p 163) (nonnegative1752 p) (nonnegative1696 p)
def d5870 (p : Pattern) : Int := if p 162 then d5862 p else d5869 p
theorem agree5870 (p q : Pattern) (h : Agree support p q) : d5870 p = d5870 q := by
  simp only [d5870, h 162 (by decide), agree5862 p q h, agree5869 p q h]
theorem nonnegative5870 (p : Pattern) : 0 ≤ d5870 p :=
  nonnegative_ite (p 162) (nonnegative5862 p) (nonnegative5869 p)
def d5871 (p : Pattern) : Int := if p 161 then d5870 p else d5868 p
theorem agree5871 (p q : Pattern) (h : Agree support p q) : d5871 p = d5871 q := by
  simp only [d5871, h 161 (by decide), agree5870 p q h, agree5868 p q h]
theorem nonnegative5871 (p : Pattern) : 0 ≤ d5871 p :=
  nonnegative_ite (p 161) (nonnegative5870 p) (nonnegative5868 p)
def d5872 (p : Pattern) : Int := if p 163 then d12 p else d1724 p
theorem agree5872 (p q : Pattern) (h : Agree support p q) : d5872 p = d5872 q := by
  simp only [d5872, h 163 (by decide), agree12 p q h, agree1724 p q h]
theorem nonnegative5872 (p : Pattern) : 0 ≤ d5872 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1724 p)
def d5873 (p : Pattern) : Int := if p 162 then d12 p else d5872 p
theorem agree5873 (p q : Pattern) (h : Agree support p q) : d5873 p = d5873 q := by
  simp only [d5873, h 162 (by decide), agree12 p q h, agree5872 p q h]
theorem nonnegative5873 (p : Pattern) : 0 ≤ d5873 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5872 p)
def d5874 (p : Pattern) : Int := if p 161 then d12 p else d5873 p
theorem agree5874 (p q : Pattern) (h : Agree support p q) : d5874 p = d5874 q := by
  simp only [d5874, h 161 (by decide), agree12 p q h, agree5873 p q h]
theorem nonnegative5874 (p : Pattern) : 0 ≤ d5874 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5873 p)
def d5875 (p : Pattern) : Int := if p 160 then d5874 p else d5871 p
theorem agree5875 (p q : Pattern) (h : Agree support p q) : d5875 p = d5875 q := by
  simp only [d5875, h 160 (by decide), agree5874 p q h, agree5871 p q h]
theorem nonnegative5875 (p : Pattern) : 0 ≤ d5875 p :=
  nonnegative_ite (p 160) (nonnegative5874 p) (nonnegative5871 p)
def d5876 (p : Pattern) : Int := if p 141 then d5875 p else d5865 p
theorem agree5876 (p q : Pattern) (h : Agree support p q) : d5876 p = d5876 q := by
  simp only [d5876, h 141 (by decide), agree5875 p q h, agree5865 p q h]
theorem nonnegative5876 (p : Pattern) : 0 ≤ d5876 p :=
  nonnegative_ite (p 141) (nonnegative5875 p) (nonnegative5865 p)
def d5877 (p : Pattern) : Int := if p 163 then d1781 p else d1772 p
theorem agree5877 (p q : Pattern) (h : Agree support p q) : d5877 p = d5877 q := by
  simp only [d5877, h 163 (by decide), agree1781 p q h, agree1772 p q h]
theorem nonnegative5877 (p : Pattern) : 0 ≤ d5877 p :=
  nonnegative_ite (p 163) (nonnegative1781 p) (nonnegative1772 p)
def d5878 (p : Pattern) : Int := if p 163 then d1797 p else d1788 p
theorem agree5878 (p q : Pattern) (h : Agree support p q) : d5878 p = d5878 q := by
  simp only [d5878, h 163 (by decide), agree1797 p q h, agree1788 p q h]
theorem nonnegative5878 (p : Pattern) : 0 ≤ d5878 p :=
  nonnegative_ite (p 163) (nonnegative1797 p) (nonnegative1788 p)
def d5879 (p : Pattern) : Int := if p 162 then d5878 p else d5877 p
theorem agree5879 (p q : Pattern) (h : Agree support p q) : d5879 p = d5879 q := by
  simp only [d5879, h 162 (by decide), agree5878 p q h, agree5877 p q h]
theorem nonnegative5879 (p : Pattern) : 0 ≤ d5879 p :=
  nonnegative_ite (p 162) (nonnegative5878 p) (nonnegative5877 p)
end NetHack.Sokoban22Refined85
