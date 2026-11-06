/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes39
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d4800 (p : Pattern) : Int := if p 138 then d12 p else d82 p
theorem agree4800 (p q : Pattern) (h : Agree support p q) : d4800 p = d4800 q := by
  simp only [d4800, h 138 (by decide), agree12 p q h, agree82 p q h]
theorem nonnegative4800 (p : Pattern) : 0 ≤ d4800 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative82 p)
def d4801 (p : Pattern) : Int := if p 116 then d4800 p else d4797 p
theorem agree4801 (p q : Pattern) (h : Agree support p q) : d4801 p = d4801 q := by
  simp only [d4801, h 116 (by decide), agree4800 p q h, agree4797 p q h]
theorem nonnegative4801 (p : Pattern) : 0 ≤ d4801 p :=
  nonnegative_ite (p 116) (nonnegative4800 p) (nonnegative4797 p)
def d4802 (p : Pattern) : Int := if p 115 then d4801 p else d4799 p
theorem agree4802 (p q : Pattern) (h : Agree support p q) : d4802 p = d4802 q := by
  simp only [d4802, h 115 (by decide), agree4801 p q h, agree4799 p q h]
theorem nonnegative4802 (p : Pattern) : 0 ≤ d4802 p :=
  nonnegative_ite (p 115) (nonnegative4801 p) (nonnegative4799 p)
def d4803 (p : Pattern) : Int := if p 138 then d152 p else d131 p
theorem agree4803 (p q : Pattern) (h : Agree support p q) : d4803 p = d4803 q := by
  simp only [d4803, h 138 (by decide), agree152 p q h, agree131 p q h]
theorem nonnegative4803 (p : Pattern) : 0 ≤ d4803 p :=
  nonnegative_ite (p 138) (nonnegative152 p) (nonnegative131 p)
def d4804 (p : Pattern) : Int := if p 138 then d161 p else d152 p
theorem agree4804 (p q : Pattern) (h : Agree support p q) : d4804 p = d4804 q := by
  simp only [d4804, h 138 (by decide), agree161 p q h, agree152 p q h]
theorem nonnegative4804 (p : Pattern) : 0 ≤ d4804 p :=
  nonnegative_ite (p 138) (nonnegative161 p) (nonnegative152 p)
def d4805 (p : Pattern) : Int := if p 116 then d4804 p else d4803 p
theorem agree4805 (p q : Pattern) (h : Agree support p q) : d4805 p = d4805 q := by
  simp only [d4805, h 116 (by decide), agree4804 p q h, agree4803 p q h]
theorem nonnegative4805 (p : Pattern) : 0 ≤ d4805 p :=
  nonnegative_ite (p 116) (nonnegative4804 p) (nonnegative4803 p)
def d4806 (p : Pattern) : Int := if p 138 then d12 p else d152 p
theorem agree4806 (p q : Pattern) (h : Agree support p q) : d4806 p = d4806 q := by
  simp only [d4806, h 138 (by decide), agree12 p q h, agree152 p q h]
theorem nonnegative4806 (p : Pattern) : 0 ≤ d4806 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative152 p)
def d4807 (p : Pattern) : Int := if p 116 then d4806 p else d4803 p
theorem agree4807 (p q : Pattern) (h : Agree support p q) : d4807 p = d4807 q := by
  simp only [d4807, h 116 (by decide), agree4806 p q h, agree4803 p q h]
theorem nonnegative4807 (p : Pattern) : 0 ≤ d4807 p :=
  nonnegative_ite (p 116) (nonnegative4806 p) (nonnegative4803 p)
def d4808 (p : Pattern) : Int := if p 115 then d4807 p else d4805 p
theorem agree4808 (p q : Pattern) (h : Agree support p q) : d4808 p = d4808 q := by
  simp only [d4808, h 115 (by decide), agree4807 p q h, agree4805 p q h]
theorem nonnegative4808 (p : Pattern) : 0 ≤ d4808 p :=
  nonnegative_ite (p 115) (nonnegative4807 p) (nonnegative4805 p)
def d4809 (p : Pattern) : Int := if p 71 then d4808 p else d4802 p
theorem agree4809 (p q : Pattern) (h : Agree support p q) : d4809 p = d4809 q := by
  simp only [d4809, h 71 (by decide), agree4808 p q h, agree4802 p q h]
theorem nonnegative4809 (p : Pattern) : 0 ≤ d4809 p :=
  nonnegative_ite (p 71) (nonnegative4808 p) (nonnegative4802 p)
def d4810 (p : Pattern) : Int := if p 49 then d4809 p else d4802 p
theorem agree4810 (p q : Pattern) (h : Agree support p q) : d4810 p = d4810 q := by
  simp only [d4810, h 49 (by decide), agree4809 p q h, agree4802 p q h]
theorem nonnegative4810 (p : Pattern) : 0 ≤ d4810 p :=
  nonnegative_ite (p 49) (nonnegative4809 p) (nonnegative4802 p)
def d4811 (p : Pattern) : Int := if p 138 then d297 p else d281 p
theorem agree4811 (p q : Pattern) (h : Agree support p q) : d4811 p = d4811 q := by
  simp only [d4811, h 138 (by decide), agree297 p q h, agree281 p q h]
theorem nonnegative4811 (p : Pattern) : 0 ≤ d4811 p :=
  nonnegative_ite (p 138) (nonnegative297 p) (nonnegative281 p)
def d4812 (p : Pattern) : Int := if p 138 then d12 p else d297 p
theorem agree4812 (p q : Pattern) (h : Agree support p q) : d4812 p = d4812 q := by
  simp only [d4812, h 138 (by decide), agree12 p q h, agree297 p q h]
theorem nonnegative4812 (p : Pattern) : 0 ≤ d4812 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative297 p)
def d4813 (p : Pattern) : Int := if p 116 then d4812 p else d4811 p
theorem agree4813 (p q : Pattern) (h : Agree support p q) : d4813 p = d4813 q := by
  simp only [d4813, h 116 (by decide), agree4812 p q h, agree4811 p q h]
theorem nonnegative4813 (p : Pattern) : 0 ≤ d4813 p :=
  nonnegative_ite (p 116) (nonnegative4812 p) (nonnegative4811 p)
def d4814 (p : Pattern) : Int := if p 115 then d4813 p else d4805 p
theorem agree4814 (p q : Pattern) (h : Agree support p q) : d4814 p = d4814 q := by
  simp only [d4814, h 115 (by decide), agree4813 p q h, agree4805 p q h]
theorem nonnegative4814 (p : Pattern) : 0 ≤ d4814 p :=
  nonnegative_ite (p 115) (nonnegative4813 p) (nonnegative4805 p)
def d4815 (p : Pattern) : Int := if p 71 then d4814 p else d4802 p
theorem agree4815 (p q : Pattern) (h : Agree support p q) : d4815 p = d4815 q := by
  simp only [d4815, h 71 (by decide), agree4814 p q h, agree4802 p q h]
theorem nonnegative4815 (p : Pattern) : 0 ≤ d4815 p :=
  nonnegative_ite (p 71) (nonnegative4814 p) (nonnegative4802 p)
def d4816 (p : Pattern) : Int := if p 49 then d4815 p else d4802 p
theorem agree4816 (p q : Pattern) (h : Agree support p q) : d4816 p = d4816 q := by
  simp only [d4816, h 49 (by decide), agree4815 p q h, agree4802 p q h]
theorem nonnegative4816 (p : Pattern) : 0 ≤ d4816 p :=
  nonnegative_ite (p 49) (nonnegative4815 p) (nonnegative4802 p)
def d4817 (p : Pattern) : Int := if p 48 then d4816 p else d4810 p
theorem agree4817 (p q : Pattern) (h : Agree support p q) : d4817 p = d4817 q := by
  simp only [d4817, h 48 (by decide), agree4816 p q h, agree4810 p q h]
theorem nonnegative4817 (p : Pattern) : 0 ≤ d4817 p :=
  nonnegative_ite (p 48) (nonnegative4816 p) (nonnegative4810 p)
def d4818 (p : Pattern) : Int := if p 160 then d47 p else d950 p
theorem agree4818 (p q : Pattern) (h : Agree support p q) : d4818 p = d4818 q := by
  simp only [d4818, h 160 (by decide), agree47 p q h, agree950 p q h]
theorem nonnegative4818 (p : Pattern) : 0 ≤ d4818 p :=
  nonnegative_ite (p 160) (nonnegative47 p) (nonnegative950 p)
def d4819 (p : Pattern) : Int := if p 160 then d176 p else d796 p
theorem agree4819 (p q : Pattern) (h : Agree support p q) : d4819 p = d4819 q := by
  simp only [d4819, h 160 (by decide), agree176 p q h, agree796 p q h]
theorem nonnegative4819 (p : Pattern) : 0 ≤ d4819 p :=
  nonnegative_ite (p 160) (nonnegative176 p) (nonnegative796 p)
def d4820 (p : Pattern) : Int := if p 141 then d4819 p else d4818 p
theorem agree4820 (p q : Pattern) (h : Agree support p q) : d4820 p = d4820 q := by
  simp only [d4820, h 141 (by decide), agree4819 p q h, agree4818 p q h]
theorem nonnegative4820 (p : Pattern) : 0 ≤ d4820 p :=
  nonnegative_ite (p 141) (nonnegative4819 p) (nonnegative4818 p)
def d4821 (p : Pattern) : Int := if p 160 then d12 p else d54 p
theorem agree4821 (p q : Pattern) (h : Agree support p q) : d4821 p = d4821 q := by
  simp only [d4821, h 160 (by decide), agree12 p q h, agree54 p q h]
theorem nonnegative4821 (p : Pattern) : 0 ≤ d4821 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative54 p)
def d4822 (p : Pattern) : Int := if p 160 then d12 p else d808 p
theorem agree4822 (p q : Pattern) (h : Agree support p q) : d4822 p = d4822 q := by
  simp only [d4822, h 160 (by decide), agree12 p q h, agree808 p q h]
theorem nonnegative4822 (p : Pattern) : 0 ≤ d4822 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative808 p)
def d4823 (p : Pattern) : Int := if p 141 then d4822 p else d4821 p
theorem agree4823 (p q : Pattern) (h : Agree support p q) : d4823 p = d4823 q := by
  simp only [d4823, h 141 (by decide), agree4822 p q h, agree4821 p q h]
theorem nonnegative4823 (p : Pattern) : 0 ≤ d4823 p :=
  nonnegative_ite (p 141) (nonnegative4822 p) (nonnegative4821 p)
def d4824 (p : Pattern) : Int := if p 138 then d4823 p else d4820 p
theorem agree4824 (p q : Pattern) (h : Agree support p q) : d4824 p = d4824 q := by
  simp only [d4824, h 138 (by decide), agree4823 p q h, agree4820 p q h]
theorem nonnegative4824 (p : Pattern) : 0 ≤ d4824 p :=
  nonnegative_ite (p 138) (nonnegative4823 p) (nonnegative4820 p)
def d4825 (p : Pattern) : Int := if p 138 then d4626 p else d4823 p
theorem agree4825 (p q : Pattern) (h : Agree support p q) : d4825 p = d4825 q := by
  simp only [d4825, h 138 (by decide), agree4626 p q h, agree4823 p q h]
theorem nonnegative4825 (p : Pattern) : 0 ≤ d4825 p :=
  nonnegative_ite (p 138) (nonnegative4626 p) (nonnegative4823 p)
def d4826 (p : Pattern) : Int := if p 116 then d4825 p else d4824 p
theorem agree4826 (p q : Pattern) (h : Agree support p q) : d4826 p = d4826 q := by
  simp only [d4826, h 116 (by decide), agree4825 p q h, agree4824 p q h]
theorem nonnegative4826 (p : Pattern) : 0 ≤ d4826 p :=
  nonnegative_ite (p 116) (nonnegative4825 p) (nonnegative4824 p)
def d4827 (p : Pattern) : Int := if p 138 then d12 p else d4823 p
theorem agree4827 (p q : Pattern) (h : Agree support p q) : d4827 p = d4827 q := by
  simp only [d4827, h 138 (by decide), agree12 p q h, agree4823 p q h]
theorem nonnegative4827 (p : Pattern) : 0 ≤ d4827 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4823 p)
def d4828 (p : Pattern) : Int := if p 116 then d4827 p else d4824 p
theorem agree4828 (p q : Pattern) (h : Agree support p q) : d4828 p = d4828 q := by
  simp only [d4828, h 116 (by decide), agree4827 p q h, agree4824 p q h]
theorem nonnegative4828 (p : Pattern) : 0 ≤ d4828 p :=
  nonnegative_ite (p 116) (nonnegative4827 p) (nonnegative4824 p)
def d4829 (p : Pattern) : Int := if p 115 then d4828 p else d4826 p
theorem agree4829 (p q : Pattern) (h : Agree support p q) : d4829 p = d4829 q := by
  simp only [d4829, h 115 (by decide), agree4828 p q h, agree4826 p q h]
theorem nonnegative4829 (p : Pattern) : 0 ≤ d4829 p :=
  nonnegative_ite (p 115) (nonnegative4828 p) (nonnegative4826 p)
def d4830 (p : Pattern) : Int := if p 160 then d126 p else d1043 p
theorem agree4830 (p q : Pattern) (h : Agree support p q) : d4830 p = d4830 q := by
  simp only [d4830, h 160 (by decide), agree126 p q h, agree1043 p q h]
theorem nonnegative4830 (p : Pattern) : 0 ≤ d4830 p :=
  nonnegative_ite (p 160) (nonnegative126 p) (nonnegative1043 p)
def d4831 (p : Pattern) : Int := if p 160 then d1053 p else d862 p
theorem agree4831 (p q : Pattern) (h : Agree support p q) : d4831 p = d4831 q := by
  simp only [d4831, h 160 (by decide), agree1053 p q h, agree862 p q h]
theorem nonnegative4831 (p : Pattern) : 0 ≤ d4831 p :=
  nonnegative_ite (p 160) (nonnegative1053 p) (nonnegative862 p)
def d4832 (p : Pattern) : Int := if p 141 then d4831 p else d4830 p
theorem agree4832 (p q : Pattern) (h : Agree support p q) : d4832 p = d4832 q := by
  simp only [d4832, h 141 (by decide), agree4831 p q h, agree4830 p q h]
theorem nonnegative4832 (p : Pattern) : 0 ≤ d4832 p :=
  nonnegative_ite (p 141) (nonnegative4831 p) (nonnegative4830 p)
def d4833 (p : Pattern) : Int := if p 160 then d12 p else d133 p
theorem agree4833 (p q : Pattern) (h : Agree support p q) : d4833 p = d4833 q := by
  simp only [d4833, h 160 (by decide), agree12 p q h, agree133 p q h]
theorem nonnegative4833 (p : Pattern) : 0 ≤ d4833 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative133 p)
def d4834 (p : Pattern) : Int := if p 160 then d12 p else d873 p
theorem agree4834 (p q : Pattern) (h : Agree support p q) : d4834 p = d4834 q := by
  simp only [d4834, h 160 (by decide), agree12 p q h, agree873 p q h]
theorem nonnegative4834 (p : Pattern) : 0 ≤ d4834 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative873 p)
def d4835 (p : Pattern) : Int := if p 141 then d4834 p else d4833 p
theorem agree4835 (p q : Pattern) (h : Agree support p q) : d4835 p = d4835 q := by
  simp only [d4835, h 141 (by decide), agree4834 p q h, agree4833 p q h]
theorem nonnegative4835 (p : Pattern) : 0 ≤ d4835 p :=
  nonnegative_ite (p 141) (nonnegative4834 p) (nonnegative4833 p)
def d4836 (p : Pattern) : Int := if p 138 then d4835 p else d4832 p
theorem agree4836 (p q : Pattern) (h : Agree support p q) : d4836 p = d4836 q := by
  simp only [d4836, h 138 (by decide), agree4835 p q h, agree4832 p q h]
theorem nonnegative4836 (p : Pattern) : 0 ≤ d4836 p :=
  nonnegative_ite (p 138) (nonnegative4835 p) (nonnegative4832 p)
def d4837 (p : Pattern) : Int := if p 138 then d12 p else d4835 p
theorem agree4837 (p q : Pattern) (h : Agree support p q) : d4837 p = d4837 q := by
  simp only [d4837, h 138 (by decide), agree12 p q h, agree4835 p q h]
theorem nonnegative4837 (p : Pattern) : 0 ≤ d4837 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4835 p)
def d4838 (p : Pattern) : Int := if p 116 then d4837 p else d4836 p
theorem agree4838 (p q : Pattern) (h : Agree support p q) : d4838 p = d4838 q := by
  simp only [d4838, h 116 (by decide), agree4837 p q h, agree4836 p q h]
theorem nonnegative4838 (p : Pattern) : 0 ≤ d4838 p :=
  nonnegative_ite (p 116) (nonnegative4837 p) (nonnegative4836 p)
def d4839 (p : Pattern) : Int := if p 71 then d4838 p else d4829 p
theorem agree4839 (p q : Pattern) (h : Agree support p q) : d4839 p = d4839 q := by
  simp only [d4839, h 71 (by decide), agree4838 p q h, agree4829 p q h]
theorem nonnegative4839 (p : Pattern) : 0 ≤ d4839 p :=
  nonnegative_ite (p 71) (nonnegative4838 p) (nonnegative4829 p)
def d4840 (p : Pattern) : Int := if p 49 then d4839 p else d4829 p
theorem agree4840 (p q : Pattern) (h : Agree support p q) : d4840 p = d4840 q := by
  simp only [d4840, h 49 (by decide), agree4839 p q h, agree4829 p q h]
theorem nonnegative4840 (p : Pattern) : 0 ≤ d4840 p :=
  nonnegative_ite (p 49) (nonnegative4839 p) (nonnegative4829 p)
def d4841 (p : Pattern) : Int := if p 160 then d275 p else d291 p
theorem agree4841 (p q : Pattern) (h : Agree support p q) : d4841 p = d4841 q := by
  simp only [d4841, h 160 (by decide), agree275 p q h, agree291 p q h]
theorem nonnegative4841 (p : Pattern) : 0 ≤ d4841 p :=
  nonnegative_ite (p 160) (nonnegative275 p) (nonnegative291 p)
def d4842 (p : Pattern) : Int := if p 160 then d1128 p else d925 p
theorem agree4842 (p q : Pattern) (h : Agree support p q) : d4842 p = d4842 q := by
  simp only [d4842, h 160 (by decide), agree1128 p q h, agree925 p q h]
theorem nonnegative4842 (p : Pattern) : 0 ≤ d4842 p :=
  nonnegative_ite (p 160) (nonnegative1128 p) (nonnegative925 p)
def d4843 (p : Pattern) : Int := if p 141 then d4842 p else d4841 p
theorem agree4843 (p q : Pattern) (h : Agree support p q) : d4843 p = d4843 q := by
  simp only [d4843, h 141 (by decide), agree4842 p q h, agree4841 p q h]
theorem nonnegative4843 (p : Pattern) : 0 ≤ d4843 p :=
  nonnegative_ite (p 141) (nonnegative4842 p) (nonnegative4841 p)
def d4844 (p : Pattern) : Int := if p 160 then d12 p else d1133 p
theorem agree4844 (p q : Pattern) (h : Agree support p q) : d4844 p = d4844 q := by
  simp only [d4844, h 160 (by decide), agree12 p q h, agree1133 p q h]
theorem nonnegative4844 (p : Pattern) : 0 ≤ d4844 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative1133 p)
def d4845 (p : Pattern) : Int := if p 160 then d12 p else d1137 p
theorem agree4845 (p q : Pattern) (h : Agree support p q) : d4845 p = d4845 q := by
  simp only [d4845, h 160 (by decide), agree12 p q h, agree1137 p q h]
theorem nonnegative4845 (p : Pattern) : 0 ≤ d4845 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative1137 p)
def d4846 (p : Pattern) : Int := if p 141 then d4845 p else d4844 p
theorem agree4846 (p q : Pattern) (h : Agree support p q) : d4846 p = d4846 q := by
  simp only [d4846, h 141 (by decide), agree4845 p q h, agree4844 p q h]
theorem nonnegative4846 (p : Pattern) : 0 ≤ d4846 p :=
  nonnegative_ite (p 141) (nonnegative4845 p) (nonnegative4844 p)
def d4847 (p : Pattern) : Int := if p 138 then d4846 p else d4843 p
theorem agree4847 (p q : Pattern) (h : Agree support p q) : d4847 p = d4847 q := by
  simp only [d4847, h 138 (by decide), agree4846 p q h, agree4843 p q h]
theorem nonnegative4847 (p : Pattern) : 0 ≤ d4847 p :=
  nonnegative_ite (p 138) (nonnegative4846 p) (nonnegative4843 p)
def d4848 (p : Pattern) : Int := if p 138 then d12 p else d4846 p
theorem agree4848 (p q : Pattern) (h : Agree support p q) : d4848 p = d4848 q := by
  simp only [d4848, h 138 (by decide), agree12 p q h, agree4846 p q h]
theorem nonnegative4848 (p : Pattern) : 0 ≤ d4848 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4846 p)
def d4849 (p : Pattern) : Int := if p 116 then d4848 p else d4847 p
theorem agree4849 (p q : Pattern) (h : Agree support p q) : d4849 p = d4849 q := by
  simp only [d4849, h 116 (by decide), agree4848 p q h, agree4847 p q h]
theorem nonnegative4849 (p : Pattern) : 0 ≤ d4849 p :=
  nonnegative_ite (p 116) (nonnegative4848 p) (nonnegative4847 p)
def d4850 (p : Pattern) : Int := if p 115 then d4849 p else d4838 p
theorem agree4850 (p q : Pattern) (h : Agree support p q) : d4850 p = d4850 q := by
  simp only [d4850, h 115 (by decide), agree4849 p q h, agree4838 p q h]
theorem nonnegative4850 (p : Pattern) : 0 ≤ d4850 p :=
  nonnegative_ite (p 115) (nonnegative4849 p) (nonnegative4838 p)
def d4851 (p : Pattern) : Int := if p 71 then d4850 p else d4829 p
theorem agree4851 (p q : Pattern) (h : Agree support p q) : d4851 p = d4851 q := by
  simp only [d4851, h 71 (by decide), agree4850 p q h, agree4829 p q h]
theorem nonnegative4851 (p : Pattern) : 0 ≤ d4851 p :=
  nonnegative_ite (p 71) (nonnegative4850 p) (nonnegative4829 p)
def d4852 (p : Pattern) : Int := if p 49 then d4851 p else d4829 p
theorem agree4852 (p q : Pattern) (h : Agree support p q) : d4852 p = d4852 q := by
  simp only [d4852, h 49 (by decide), agree4851 p q h, agree4829 p q h]
theorem nonnegative4852 (p : Pattern) : 0 ≤ d4852 p :=
  nonnegative_ite (p 49) (nonnegative4851 p) (nonnegative4829 p)
def d4853 (p : Pattern) : Int := if p 48 then d4852 p else d4840 p
theorem agree4853 (p q : Pattern) (h : Agree support p q) : d4853 p = d4853 q := by
  simp only [d4853, h 48 (by decide), agree4852 p q h, agree4840 p q h]
theorem nonnegative4853 (p : Pattern) : 0 ≤ d4853 p :=
  nonnegative_ite (p 48) (nonnegative4852 p) (nonnegative4840 p)
def d4854 (p : Pattern) : Int := if p 161 then d26 p else d16 p
theorem agree4854 (p q : Pattern) (h : Agree support p q) : d4854 p = d4854 q := by
  simp only [d4854, h 161 (by decide), agree26 p q h, agree16 p q h]
theorem nonnegative4854 (p : Pattern) : 0 ≤ d4854 p :=
  nonnegative_ite (p 161) (nonnegative26 p) (nonnegative16 p)
def d4855 (p : Pattern) : Int := if p 161 then d48 p else d42 p
theorem agree4855 (p q : Pattern) (h : Agree support p q) : d4855 p = d4855 q := by
  simp only [d4855, h 161 (by decide), agree48 p q h, agree42 p q h]
theorem nonnegative4855 (p : Pattern) : 0 ≤ d4855 p :=
  nonnegative_ite (p 161) (nonnegative48 p) (nonnegative42 p)
def d4856 (p : Pattern) : Int := if p 160 then d4855 p else d4854 p
theorem agree4856 (p q : Pattern) (h : Agree support p q) : d4856 p = d4856 q := by
  simp only [d4856, h 160 (by decide), agree4855 p q h, agree4854 p q h]
theorem nonnegative4856 (p : Pattern) : 0 ≤ d4856 p :=
  nonnegative_ite (p 160) (nonnegative4855 p) (nonnegative4854 p)
def d4857 (p : Pattern) : Int := if p 161 then d62 p else d53 p
theorem agree4857 (p q : Pattern) (h : Agree support p q) : d4857 p = d4857 q := by
  simp only [d4857, h 161 (by decide), agree62 p q h, agree53 p q h]
theorem nonnegative4857 (p : Pattern) : 0 ≤ d4857 p :=
  nonnegative_ite (p 161) (nonnegative62 p) (nonnegative53 p)
def d4858 (p : Pattern) : Int := if p 161 then d72 p else d66 p
theorem agree4858 (p q : Pattern) (h : Agree support p q) : d4858 p = d4858 q := by
  simp only [d4858, h 161 (by decide), agree72 p q h, agree66 p q h]
theorem nonnegative4858 (p : Pattern) : 0 ≤ d4858 p :=
  nonnegative_ite (p 161) (nonnegative72 p) (nonnegative66 p)
def d4859 (p : Pattern) : Int := if p 160 then d4858 p else d4857 p
theorem agree4859 (p q : Pattern) (h : Agree support p q) : d4859 p = d4859 q := by
  simp only [d4859, h 160 (by decide), agree4858 p q h, agree4857 p q h]
theorem nonnegative4859 (p : Pattern) : 0 ≤ d4859 p :=
  nonnegative_ite (p 160) (nonnegative4858 p) (nonnegative4857 p)
def d4860 (p : Pattern) : Int := if p 141 then d4859 p else d4856 p
theorem agree4860 (p q : Pattern) (h : Agree support p q) : d4860 p = d4860 q := by
  simp only [d4860, h 141 (by decide), agree4859 p q h, agree4856 p q h]
theorem nonnegative4860 (p : Pattern) : 0 ≤ d4860 p :=
  nonnegative_ite (p 141) (nonnegative4859 p) (nonnegative4856 p)
def d4861 (p : Pattern) : Int := if p 160 then d4689 p else d4854 p
theorem agree4861 (p q : Pattern) (h : Agree support p q) : d4861 p = d4861 q := by
  simp only [d4861, h 160 (by decide), agree4689 p q h, agree4854 p q h]
theorem nonnegative4861 (p : Pattern) : 0 ≤ d4861 p :=
  nonnegative_ite (p 160) (nonnegative4689 p) (nonnegative4854 p)
def d4862 (p : Pattern) : Int := if p 160 then d12 p else d4857 p
theorem agree4862 (p q : Pattern) (h : Agree support p q) : d4862 p = d4862 q := by
  simp only [d4862, h 160 (by decide), agree12 p q h, agree4857 p q h]
theorem nonnegative4862 (p : Pattern) : 0 ≤ d4862 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4857 p)
def d4863 (p : Pattern) : Int := if p 141 then d4862 p else d4861 p
theorem agree4863 (p q : Pattern) (h : Agree support p q) : d4863 p = d4863 q := by
  simp only [d4863, h 141 (by decide), agree4862 p q h, agree4861 p q h]
theorem nonnegative4863 (p : Pattern) : 0 ≤ d4863 p :=
  nonnegative_ite (p 141) (nonnegative4862 p) (nonnegative4861 p)
def d4864 (p : Pattern) : Int := if p 138 then d4863 p else d4860 p
theorem agree4864 (p q : Pattern) (h : Agree support p q) : d4864 p = d4864 q := by
  simp only [d4864, h 138 (by decide), agree4863 p q h, agree4860 p q h]
theorem nonnegative4864 (p : Pattern) : 0 ≤ d4864 p :=
  nonnegative_ite (p 138) (nonnegative4863 p) (nonnegative4860 p)
def d4865 (p : Pattern) : Int := if p 138 then d4691 p else d4863 p
theorem agree4865 (p q : Pattern) (h : Agree support p q) : d4865 p = d4865 q := by
  simp only [d4865, h 138 (by decide), agree4691 p q h, agree4863 p q h]
theorem nonnegative4865 (p : Pattern) : 0 ≤ d4865 p :=
  nonnegative_ite (p 138) (nonnegative4691 p) (nonnegative4863 p)
def d4866 (p : Pattern) : Int := if p 116 then d4865 p else d4864 p
theorem agree4866 (p q : Pattern) (h : Agree support p q) : d4866 p = d4866 q := by
  simp only [d4866, h 116 (by decide), agree4865 p q h, agree4864 p q h]
theorem nonnegative4866 (p : Pattern) : 0 ≤ d4866 p :=
  nonnegative_ite (p 116) (nonnegative4865 p) (nonnegative4864 p)
def d4867 (p : Pattern) : Int := if p 138 then d12 p else d4863 p
theorem agree4867 (p q : Pattern) (h : Agree support p q) : d4867 p = d4867 q := by
  simp only [d4867, h 138 (by decide), agree12 p q h, agree4863 p q h]
theorem nonnegative4867 (p : Pattern) : 0 ≤ d4867 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4863 p)
def d4868 (p : Pattern) : Int := if p 116 then d4867 p else d4864 p
theorem agree4868 (p q : Pattern) (h : Agree support p q) : d4868 p = d4868 q := by
  simp only [d4868, h 116 (by decide), agree4867 p q h, agree4864 p q h]
theorem nonnegative4868 (p : Pattern) : 0 ≤ d4868 p :=
  nonnegative_ite (p 116) (nonnegative4867 p) (nonnegative4864 p)
def d4869 (p : Pattern) : Int := if p 115 then d4868 p else d4866 p
theorem agree4869 (p q : Pattern) (h : Agree support p q) : d4869 p = d4869 q := by
  simp only [d4869, h 115 (by decide), agree4868 p q h, agree4866 p q h]
theorem nonnegative4869 (p : Pattern) : 0 ≤ d4869 p :=
  nonnegative_ite (p 115) (nonnegative4868 p) (nonnegative4866 p)
def d4870 (p : Pattern) : Int := if p 161 then d60 p else d105 p
theorem agree4870 (p q : Pattern) (h : Agree support p q) : d4870 p = d4870 q := by
  simp only [d4870, h 161 (by decide), agree60 p q h, agree105 p q h]
theorem nonnegative4870 (p : Pattern) : 0 ≤ d4870 p :=
  nonnegative_ite (p 161) (nonnegative60 p) (nonnegative105 p)
def d4871 (p : Pattern) : Int := if p 161 then d70 p else d124 p
theorem agree4871 (p q : Pattern) (h : Agree support p q) : d4871 p = d4871 q := by
  simp only [d4871, h 161 (by decide), agree70 p q h, agree124 p q h]
theorem nonnegative4871 (p : Pattern) : 0 ≤ d4871 p :=
  nonnegative_ite (p 161) (nonnegative70 p) (nonnegative124 p)
def d4872 (p : Pattern) : Int := if p 160 then d4871 p else d4870 p
theorem agree4872 (p q : Pattern) (h : Agree support p q) : d4872 p = d4872 q := by
  simp only [d4872, h 160 (by decide), agree4871 p q h, agree4870 p q h]
theorem nonnegative4872 (p : Pattern) : 0 ≤ d4872 p :=
  nonnegative_ite (p 160) (nonnegative4871 p) (nonnegative4870 p)
def d4873 (p : Pattern) : Int := if p 161 then d12 p else d139 p
theorem agree4873 (p q : Pattern) (h : Agree support p q) : d4873 p = d4873 q := by
  simp only [d4873, h 161 (by decide), agree12 p q h, agree139 p q h]
theorem nonnegative4873 (p : Pattern) : 0 ≤ d4873 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative139 p)
def d4874 (p : Pattern) : Int := if p 160 then d4873 p else d4705 p
theorem agree4874 (p q : Pattern) (h : Agree support p q) : d4874 p = d4874 q := by
  simp only [d4874, h 160 (by decide), agree4873 p q h, agree4705 p q h]
theorem nonnegative4874 (p : Pattern) : 0 ≤ d4874 p :=
  nonnegative_ite (p 160) (nonnegative4873 p) (nonnegative4705 p)
def d4875 (p : Pattern) : Int := if p 141 then d4874 p else d4872 p
theorem agree4875 (p q : Pattern) (h : Agree support p q) : d4875 p = d4875 q := by
  simp only [d4875, h 141 (by decide), agree4874 p q h, agree4872 p q h]
theorem nonnegative4875 (p : Pattern) : 0 ≤ d4875 p :=
  nonnegative_ite (p 141) (nonnegative4874 p) (nonnegative4872 p)
def d4876 (p : Pattern) : Int := if p 160 then d12 p else d4870 p
theorem agree4876 (p q : Pattern) (h : Agree support p q) : d4876 p = d4876 q := by
  simp only [d4876, h 160 (by decide), agree12 p q h, agree4870 p q h]
theorem nonnegative4876 (p : Pattern) : 0 ≤ d4876 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4870 p)
def d4877 (p : Pattern) : Int := if p 160 then d12 p else d4705 p
theorem agree4877 (p q : Pattern) (h : Agree support p q) : d4877 p = d4877 q := by
  simp only [d4877, h 160 (by decide), agree12 p q h, agree4705 p q h]
theorem nonnegative4877 (p : Pattern) : 0 ≤ d4877 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4705 p)
def d4878 (p : Pattern) : Int := if p 141 then d4877 p else d4876 p
theorem agree4878 (p q : Pattern) (h : Agree support p q) : d4878 p = d4878 q := by
  simp only [d4878, h 141 (by decide), agree4877 p q h, agree4876 p q h]
theorem nonnegative4878 (p : Pattern) : 0 ≤ d4878 p :=
  nonnegative_ite (p 141) (nonnegative4877 p) (nonnegative4876 p)
def d4879 (p : Pattern) : Int := if p 138 then d4878 p else d4875 p
theorem agree4879 (p q : Pattern) (h : Agree support p q) : d4879 p = d4879 q := by
  simp only [d4879, h 138 (by decide), agree4878 p q h, agree4875 p q h]
theorem nonnegative4879 (p : Pattern) : 0 ≤ d4879 p :=
  nonnegative_ite (p 138) (nonnegative4878 p) (nonnegative4875 p)
def d4880 (p : Pattern) : Int := if p 138 then d12 p else d4878 p
theorem agree4880 (p q : Pattern) (h : Agree support p q) : d4880 p = d4880 q := by
  simp only [d4880, h 138 (by decide), agree12 p q h, agree4878 p q h]
theorem nonnegative4880 (p : Pattern) : 0 ≤ d4880 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4878 p)
def d4881 (p : Pattern) : Int := if p 116 then d4880 p else d4879 p
theorem agree4881 (p q : Pattern) (h : Agree support p q) : d4881 p = d4881 q := by
  simp only [d4881, h 116 (by decide), agree4880 p q h, agree4879 p q h]
theorem nonnegative4881 (p : Pattern) : 0 ≤ d4881 p :=
  nonnegative_ite (p 116) (nonnegative4880 p) (nonnegative4879 p)
def d4882 (p : Pattern) : Int := if p 71 then d4881 p else d4869 p
theorem agree4882 (p q : Pattern) (h : Agree support p q) : d4882 p = d4882 q := by
  simp only [d4882, h 71 (by decide), agree4881 p q h, agree4869 p q h]
theorem nonnegative4882 (p : Pattern) : 0 ≤ d4882 p :=
  nonnegative_ite (p 71) (nonnegative4881 p) (nonnegative4869 p)
def d4883 (p : Pattern) : Int := if p 49 then d4882 p else d4869 p
theorem agree4883 (p q : Pattern) (h : Agree support p q) : d4883 p = d4883 q := by
  simp only [d4883, h 49 (by decide), agree4882 p q h, agree4869 p q h]
theorem nonnegative4883 (p : Pattern) : 0 ≤ d4883 p :=
  nonnegative_ite (p 49) (nonnegative4882 p) (nonnegative4869 p)
def d4884 (p : Pattern) : Int := if p 161 then d277 p else d272 p
theorem agree4884 (p q : Pattern) (h : Agree support p q) : d4884 p = d4884 q := by
  simp only [d4884, h 161 (by decide), agree277 p q h, agree272 p q h]
theorem nonnegative4884 (p : Pattern) : 0 ≤ d4884 p :=
  nonnegative_ite (p 161) (nonnegative277 p) (nonnegative272 p)
def d4885 (p : Pattern) : Int := if p 160 then d4884 p else d4870 p
theorem agree4885 (p q : Pattern) (h : Agree support p q) : d4885 p = d4885 q := by
  simp only [d4885, h 160 (by decide), agree4884 p q h, agree4870 p q h]
theorem nonnegative4885 (p : Pattern) : 0 ≤ d4885 p :=
  nonnegative_ite (p 160) (nonnegative4884 p) (nonnegative4870 p)
def d4886 (p : Pattern) : Int := if p 161 then d12 p else d283 p
theorem agree4886 (p q : Pattern) (h : Agree support p q) : d4886 p = d4886 q := by
  simp only [d4886, h 161 (by decide), agree12 p q h, agree283 p q h]
theorem nonnegative4886 (p : Pattern) : 0 ≤ d4886 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative283 p)
def d4887 (p : Pattern) : Int := if p 160 then d4886 p else d4705 p
theorem agree4887 (p q : Pattern) (h : Agree support p q) : d4887 p = d4887 q := by
  simp only [d4887, h 160 (by decide), agree4886 p q h, agree4705 p q h]
theorem nonnegative4887 (p : Pattern) : 0 ≤ d4887 p :=
  nonnegative_ite (p 160) (nonnegative4886 p) (nonnegative4705 p)
def d4888 (p : Pattern) : Int := if p 141 then d4887 p else d4885 p
theorem agree4888 (p q : Pattern) (h : Agree support p q) : d4888 p = d4888 q := by
  simp only [d4888, h 141 (by decide), agree4887 p q h, agree4885 p q h]
theorem nonnegative4888 (p : Pattern) : 0 ≤ d4888 p :=
  nonnegative_ite (p 141) (nonnegative4887 p) (nonnegative4885 p)
def d4889 (p : Pattern) : Int := if p 161 then d277 p else d269 p
theorem agree4889 (p q : Pattern) (h : Agree support p q) : d4889 p = d4889 q := by
  simp only [d4889, h 161 (by decide), agree277 p q h, agree269 p q h]
theorem nonnegative4889 (p : Pattern) : 0 ≤ d4889 p :=
  nonnegative_ite (p 161) (nonnegative277 p) (nonnegative269 p)
def d4890 (p : Pattern) : Int := if p 160 then d12 p else d4889 p
theorem agree4890 (p q : Pattern) (h : Agree support p q) : d4890 p = d4890 q := by
  simp only [d4890, h 160 (by decide), agree12 p q h, agree4889 p q h]
theorem nonnegative4890 (p : Pattern) : 0 ≤ d4890 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4889 p)
def d4891 (p : Pattern) : Int := if p 161 then d12 p else d298 p
theorem agree4891 (p q : Pattern) (h : Agree support p q) : d4891 p = d4891 q := by
  simp only [d4891, h 161 (by decide), agree12 p q h, agree298 p q h]
theorem nonnegative4891 (p : Pattern) : 0 ≤ d4891 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative298 p)
def d4892 (p : Pattern) : Int := if p 160 then d12 p else d4891 p
theorem agree4892 (p q : Pattern) (h : Agree support p q) : d4892 p = d4892 q := by
  simp only [d4892, h 160 (by decide), agree12 p q h, agree4891 p q h]
theorem nonnegative4892 (p : Pattern) : 0 ≤ d4892 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4891 p)
def d4893 (p : Pattern) : Int := if p 141 then d4892 p else d4890 p
theorem agree4893 (p q : Pattern) (h : Agree support p q) : d4893 p = d4893 q := by
  simp only [d4893, h 141 (by decide), agree4892 p q h, agree4890 p q h]
theorem nonnegative4893 (p : Pattern) : 0 ≤ d4893 p :=
  nonnegative_ite (p 141) (nonnegative4892 p) (nonnegative4890 p)
def d4894 (p : Pattern) : Int := if p 138 then d4893 p else d4888 p
theorem agree4894 (p q : Pattern) (h : Agree support p q) : d4894 p = d4894 q := by
  simp only [d4894, h 138 (by decide), agree4893 p q h, agree4888 p q h]
theorem nonnegative4894 (p : Pattern) : 0 ≤ d4894 p :=
  nonnegative_ite (p 138) (nonnegative4893 p) (nonnegative4888 p)
def d4895 (p : Pattern) : Int := if p 138 then d12 p else d4893 p
theorem agree4895 (p q : Pattern) (h : Agree support p q) : d4895 p = d4895 q := by
  simp only [d4895, h 138 (by decide), agree12 p q h, agree4893 p q h]
theorem nonnegative4895 (p : Pattern) : 0 ≤ d4895 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4893 p)
def d4896 (p : Pattern) : Int := if p 116 then d4895 p else d4894 p
theorem agree4896 (p q : Pattern) (h : Agree support p q) : d4896 p = d4896 q := by
  simp only [d4896, h 116 (by decide), agree4895 p q h, agree4894 p q h]
theorem nonnegative4896 (p : Pattern) : 0 ≤ d4896 p :=
  nonnegative_ite (p 116) (nonnegative4895 p) (nonnegative4894 p)
def d4897 (p : Pattern) : Int := if p 115 then d4896 p else d4881 p
theorem agree4897 (p q : Pattern) (h : Agree support p q) : d4897 p = d4897 q := by
  simp only [d4897, h 115 (by decide), agree4896 p q h, agree4881 p q h]
theorem nonnegative4897 (p : Pattern) : 0 ≤ d4897 p :=
  nonnegative_ite (p 115) (nonnegative4896 p) (nonnegative4881 p)
def d4898 (p : Pattern) : Int := if p 71 then d4897 p else d4869 p
theorem agree4898 (p q : Pattern) (h : Agree support p q) : d4898 p = d4898 q := by
  simp only [d4898, h 71 (by decide), agree4897 p q h, agree4869 p q h]
theorem nonnegative4898 (p : Pattern) : 0 ≤ d4898 p :=
  nonnegative_ite (p 71) (nonnegative4897 p) (nonnegative4869 p)
def d4899 (p : Pattern) : Int := if p 49 then d4898 p else d4869 p
theorem agree4899 (p q : Pattern) (h : Agree support p q) : d4899 p = d4899 q := by
  simp only [d4899, h 49 (by decide), agree4898 p q h, agree4869 p q h]
theorem nonnegative4899 (p : Pattern) : 0 ≤ d4899 p :=
  nonnegative_ite (p 49) (nonnegative4898 p) (nonnegative4869 p)
def d4900 (p : Pattern) : Int := if p 48 then d4899 p else d4883 p
theorem agree4900 (p q : Pattern) (h : Agree support p q) : d4900 p = d4900 q := by
  simp only [d4900, h 48 (by decide), agree4899 p q h, agree4883 p q h]
theorem nonnegative4900 (p : Pattern) : 0 ≤ d4900 p :=
  nonnegative_ite (p 48) (nonnegative4899 p) (nonnegative4883 p)
def d4901 (p : Pattern) : Int := if p 224 then d1 p else d0 p
theorem agree4901 (p q : Pattern) (h : Agree support p q) : d4901 p = d4901 q := by
  simp only [d4901, h 224 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4901 (p : Pattern) : 0 ≤ d4901 p :=
  nonnegative_ite (p 224) (nonnegative1 p) (nonnegative0 p)
def d4902 (p : Pattern) : Int := if p 224 then d0 p else d1 p
theorem agree4902 (p q : Pattern) (h : Agree support p q) : d4902 p = d4902 q := by
  simp only [d4902, h 224 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4902 (p : Pattern) : 0 ≤ d4902 p :=
  nonnegative_ite (p 224) (nonnegative0 p) (nonnegative1 p)
def d4903 (p : Pattern) : Int := if p 161 then d12 p else d4257 p
theorem agree4903 (p q : Pattern) (h : Agree support p q) : d4903 p = d4903 q := by
  simp only [d4903, h 161 (by decide), agree12 p q h, agree4257 p q h]
theorem nonnegative4903 (p : Pattern) : 0 ≤ d4903 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4257 p)
def d4904 (p : Pattern) : Int := if p 160 then d4903 p else d4213 p
theorem agree4904 (p q : Pattern) (h : Agree support p q) : d4904 p = d4904 q := by
  simp only [d4904, h 160 (by decide), agree4903 p q h, agree4213 p q h]
theorem nonnegative4904 (p : Pattern) : 0 ≤ d4904 p :=
  nonnegative_ite (p 160) (nonnegative4903 p) (nonnegative4213 p)
def d4905 (p : Pattern) : Int := if p 161 then d12 p else d4262 p
theorem agree4905 (p q : Pattern) (h : Agree support p q) : d4905 p = d4905 q := by
  simp only [d4905, h 161 (by decide), agree12 p q h, agree4262 p q h]
theorem nonnegative4905 (p : Pattern) : 0 ≤ d4905 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4262 p)
def d4906 (p : Pattern) : Int := if p 160 then d4905 p else d4220 p
theorem agree4906 (p q : Pattern) (h : Agree support p q) : d4906 p = d4906 q := by
  simp only [d4906, h 160 (by decide), agree4905 p q h, agree4220 p q h]
theorem nonnegative4906 (p : Pattern) : 0 ≤ d4906 p :=
  nonnegative_ite (p 160) (nonnegative4905 p) (nonnegative4220 p)
def d4907 (p : Pattern) : Int := if p 141 then d4906 p else d4904 p
theorem agree4907 (p q : Pattern) (h : Agree support p q) : d4907 p = d4907 q := by
  simp only [d4907, h 141 (by decide), agree4906 p q h, agree4904 p q h]
theorem nonnegative4907 (p : Pattern) : 0 ≤ d4907 p :=
  nonnegative_ite (p 141) (nonnegative4906 p) (nonnegative4904 p)
def d4908 (p : Pattern) : Int := if p 160 then d4226 p else d4225 p
theorem agree4908 (p q : Pattern) (h : Agree support p q) : d4908 p = d4908 q := by
  simp only [d4908, h 160 (by decide), agree4226 p q h, agree4225 p q h]
theorem nonnegative4908 (p : Pattern) : 0 ≤ d4908 p :=
  nonnegative_ite (p 160) (nonnegative4226 p) (nonnegative4225 p)
def d4909 (p : Pattern) : Int := if p 160 then d12 p else d4226 p
theorem agree4909 (p q : Pattern) (h : Agree support p q) : d4909 p = d4909 q := by
  simp only [d4909, h 160 (by decide), agree12 p q h, agree4226 p q h]
theorem nonnegative4909 (p : Pattern) : 0 ≤ d4909 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4226 p)
def d4910 (p : Pattern) : Int := if p 141 then d4909 p else d4908 p
theorem agree4910 (p q : Pattern) (h : Agree support p q) : d4910 p = d4910 q := by
  simp only [d4910, h 141 (by decide), agree4909 p q h, agree4908 p q h]
theorem nonnegative4910 (p : Pattern) : 0 ≤ d4910 p :=
  nonnegative_ite (p 141) (nonnegative4909 p) (nonnegative4908 p)
def d4911 (p : Pattern) : Int := if p 138 then d4910 p else d4907 p
theorem agree4911 (p q : Pattern) (h : Agree support p q) : d4911 p = d4911 q := by
  simp only [d4911, h 138 (by decide), agree4910 p q h, agree4907 p q h]
theorem nonnegative4911 (p : Pattern) : 0 ≤ d4911 p :=
  nonnegative_ite (p 138) (nonnegative4910 p) (nonnegative4907 p)
def d4912 (p : Pattern) : Int := if p 116 then d4911 p else d4907 p
theorem agree4912 (p q : Pattern) (h : Agree support p q) : d4912 p = d4912 q := by
  simp only [d4912, h 116 (by decide), agree4911 p q h, agree4907 p q h]
theorem nonnegative4912 (p : Pattern) : 0 ≤ d4912 p :=
  nonnegative_ite (p 116) (nonnegative4911 p) (nonnegative4907 p)
def d4913 (p : Pattern) : Int := if p 138 then d12 p else d4907 p
theorem agree4913 (p q : Pattern) (h : Agree support p q) : d4913 p = d4913 q := by
  simp only [d4913, h 138 (by decide), agree12 p q h, agree4907 p q h]
theorem nonnegative4913 (p : Pattern) : 0 ≤ d4913 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4907 p)
def d4914 (p : Pattern) : Int := if p 116 then d4913 p else d4907 p
theorem agree4914 (p q : Pattern) (h : Agree support p q) : d4914 p = d4914 q := by
  simp only [d4914, h 116 (by decide), agree4913 p q h, agree4907 p q h]
theorem nonnegative4914 (p : Pattern) : 0 ≤ d4914 p :=
  nonnegative_ite (p 116) (nonnegative4913 p) (nonnegative4907 p)
def d4915 (p : Pattern) : Int := if p 115 then d4914 p else d4912 p
theorem agree4915 (p q : Pattern) (h : Agree support p q) : d4915 p = d4915 q := by
  simp only [d4915, h 115 (by decide), agree4914 p q h, agree4912 p q h]
theorem nonnegative4915 (p : Pattern) : 0 ≤ d4915 p :=
  nonnegative_ite (p 115) (nonnegative4914 p) (nonnegative4912 p)
def d4916 (p : Pattern) : Int := if p 163 then d121 p else d117 p
theorem agree4916 (p q : Pattern) (h : Agree support p q) : d4916 p = d4916 q := by
  simp only [d4916, h 163 (by decide), agree121 p q h, agree117 p q h]
theorem nonnegative4916 (p : Pattern) : 0 ≤ d4916 p :=
  nonnegative_ite (p 163) (nonnegative121 p) (nonnegative117 p)
def d4917 (p : Pattern) : Int := if p 162 then d12 p else d4916 p
theorem agree4917 (p q : Pattern) (h : Agree support p q) : d4917 p = d4917 q := by
  simp only [d4917, h 162 (by decide), agree12 p q h, agree4916 p q h]
theorem nonnegative4917 (p : Pattern) : 0 ≤ d4917 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4916 p)
def d4918 (p : Pattern) : Int := if p 161 then d12 p else d4917 p
theorem agree4918 (p q : Pattern) (h : Agree support p q) : d4918 p = d4918 q := by
  simp only [d4918, h 161 (by decide), agree12 p q h, agree4917 p q h]
theorem nonnegative4918 (p : Pattern) : 0 ≤ d4918 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4917 p)
def d4919 (p : Pattern) : Int := if p 160 then d4918 p else d4237 p
theorem agree4919 (p q : Pattern) (h : Agree support p q) : d4919 p = d4919 q := by
  simp only [d4919, h 160 (by decide), agree4918 p q h, agree4237 p q h]
theorem nonnegative4919 (p : Pattern) : 0 ≤ d4919 p :=
  nonnegative_ite (p 160) (nonnegative4918 p) (nonnegative4237 p)
end NetHack.Sokoban22Refined85
