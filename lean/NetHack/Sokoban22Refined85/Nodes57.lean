/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes56
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6840 (p : Pattern) : Int := if p 141 then d12 p else d6839 p
theorem agree6840 (p q : Pattern) (h : Agree support p q) : d6840 p = d6840 q := by
  simp only [d6840, h 141 (by decide), agree12 p q h, agree6839 p q h]
theorem nonnegative6840 (p : Pattern) : 0 ≤ d6840 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative6839 p)
def d6841 (p : Pattern) : Int := if p 138 then d6840 p else d6835 p
theorem agree6841 (p q : Pattern) (h : Agree support p q) : d6841 p = d6841 q := by
  simp only [d6841, h 138 (by decide), agree6840 p q h, agree6835 p q h]
theorem nonnegative6841 (p : Pattern) : 0 ≤ d6841 p :=
  nonnegative_ite (p 138) (nonnegative6840 p) (nonnegative6835 p)
def d6842 (p : Pattern) : Int := if p 116 then d6841 p else d6836 p
theorem agree6842 (p q : Pattern) (h : Agree support p q) : d6842 p = d6842 q := by
  simp only [d6842, h 116 (by decide), agree6841 p q h, agree6836 p q h]
theorem nonnegative6842 (p : Pattern) : 0 ≤ d6842 p :=
  nonnegative_ite (p 116) (nonnegative6841 p) (nonnegative6836 p)
def d6843 (p : Pattern) : Int := if p 138 then d12 p else d6835 p
theorem agree6843 (p q : Pattern) (h : Agree support p q) : d6843 p = d6843 q := by
  simp only [d6843, h 138 (by decide), agree12 p q h, agree6835 p q h]
theorem nonnegative6843 (p : Pattern) : 0 ≤ d6843 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6835 p)
def d6844 (p : Pattern) : Int := if p 116 then d6843 p else d6836 p
theorem agree6844 (p q : Pattern) (h : Agree support p q) : d6844 p = d6844 q := by
  simp only [d6844, h 116 (by decide), agree6843 p q h, agree6836 p q h]
theorem nonnegative6844 (p : Pattern) : 0 ≤ d6844 p :=
  nonnegative_ite (p 116) (nonnegative6843 p) (nonnegative6836 p)
def d6845 (p : Pattern) : Int := if p 115 then d6844 p else d6842 p
theorem agree6845 (p q : Pattern) (h : Agree support p q) : d6845 p = d6845 q := by
  simp only [d6845, h 115 (by decide), agree6844 p q h, agree6842 p q h]
theorem nonnegative6845 (p : Pattern) : 0 ≤ d6845 p :=
  nonnegative_ite (p 115) (nonnegative6844 p) (nonnegative6842 p)
def d6846 (p : Pattern) : Int := if p 71 then d6845 p else d6718 p
theorem agree6846 (p q : Pattern) (h : Agree support p q) : d6846 p = d6846 q := by
  simp only [d6846, h 71 (by decide), agree6845 p q h, agree6718 p q h]
theorem nonnegative6846 (p : Pattern) : 0 ≤ d6846 p :=
  nonnegative_ite (p 71) (nonnegative6845 p) (nonnegative6718 p)
def d6847 (p : Pattern) : Int := if p 49 then d6846 p else d6718 p
theorem agree6847 (p q : Pattern) (h : Agree support p q) : d6847 p = d6847 q := by
  simp only [d6847, h 49 (by decide), agree6846 p q h, agree6718 p q h]
theorem nonnegative6847 (p : Pattern) : 0 ≤ d6847 p :=
  nonnegative_ite (p 49) (nonnegative6846 p) (nonnegative6718 p)
def d6848 (p : Pattern) : Int := if p 225 then d6615 p else d6568 p
theorem agree6848 (p q : Pattern) (h : Agree support p q) : d6848 p = d6848 q := by
  simp only [d6848, h 225 (by decide), agree6615 p q h, agree6568 p q h]
theorem nonnegative6848 (p : Pattern) : 0 ≤ d6848 p :=
  nonnegative_ite (p 225) (nonnegative6615 p) (nonnegative6568 p)
def d6849 (p : Pattern) : Int := if p 224 then d6848 p else d6616 p
theorem agree6849 (p q : Pattern) (h : Agree support p q) : d6849 p = d6849 q := by
  simp only [d6849, h 224 (by decide), agree6848 p q h, agree6616 p q h]
theorem nonnegative6849 (p : Pattern) : 0 ≤ d6849 p :=
  nonnegative_ite (p 224) (nonnegative6848 p) (nonnegative6616 p)
def d6850 (p : Pattern) : Int := if p 204 then d6849 p else d4 p
theorem agree6850 (p q : Pattern) (h : Agree support p q) : d6850 p = d6850 q := by
  simp only [d6850, h 204 (by decide), agree6849 p q h, agree4 p q h]
theorem nonnegative6850 (p : Pattern) : 0 ≤ d6850 p :=
  nonnegative_ite (p 204) (nonnegative6849 p) (nonnegative4 p)
def d6851 (p : Pattern) : Int := if p 204 then d12 p else d6570 p
theorem agree6851 (p q : Pattern) (h : Agree support p q) : d6851 p = d6851 q := by
  simp only [d6851, h 204 (by decide), agree12 p q h, agree6570 p q h]
theorem nonnegative6851 (p : Pattern) : 0 ≤ d6851 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6570 p)
def d6852 (p : Pattern) : Int := if p 182 then d6851 p else d6850 p
theorem agree6852 (p q : Pattern) (h : Agree support p q) : d6852 p = d6852 q := by
  simp only [d6852, h 182 (by decide), agree6851 p q h, agree6850 p q h]
theorem nonnegative6852 (p : Pattern) : 0 ≤ d6852 p :=
  nonnegative_ite (p 182) (nonnegative6851 p) (nonnegative6850 p)
def d6853 (p : Pattern) : Int := if p 163 then d6852 p else d6669 p
theorem agree6853 (p q : Pattern) (h : Agree support p q) : d6853 p = d6853 q := by
  simp only [d6853, h 163 (by decide), agree6852 p q h, agree6669 p q h]
theorem nonnegative6853 (p : Pattern) : 0 ≤ d6853 p :=
  nonnegative_ite (p 163) (nonnegative6852 p) (nonnegative6669 p)
def d6854 (p : Pattern) : Int := if p 162 then d6853 p else d6669 p
theorem agree6854 (p q : Pattern) (h : Agree support p q) : d6854 p = d6854 q := by
  simp only [d6854, h 162 (by decide), agree6853 p q h, agree6669 p q h]
theorem nonnegative6854 (p : Pattern) : 0 ≤ d6854 p :=
  nonnegative_ite (p 162) (nonnegative6853 p) (nonnegative6669 p)
def d6855 (p : Pattern) : Int := if p 162 then d6684 p else d6853 p
theorem agree6855 (p q : Pattern) (h : Agree support p q) : d6855 p = d6855 q := by
  simp only [d6855, h 162 (by decide), agree6684 p q h, agree6853 p q h]
theorem nonnegative6855 (p : Pattern) : 0 ≤ d6855 p :=
  nonnegative_ite (p 162) (nonnegative6684 p) (nonnegative6853 p)
def d6856 (p : Pattern) : Int := if p 161 then d6855 p else d6854 p
theorem agree6856 (p q : Pattern) (h : Agree support p q) : d6856 p = d6856 q := by
  simp only [d6856, h 161 (by decide), agree6855 p q h, agree6854 p q h]
theorem nonnegative6856 (p : Pattern) : 0 ≤ d6856 p :=
  nonnegative_ite (p 161) (nonnegative6855 p) (nonnegative6854 p)
def d6857 (p : Pattern) : Int := if p 182 then d6608 p else d6652 p
theorem agree6857 (p q : Pattern) (h : Agree support p q) : d6857 p = d6857 q := by
  simp only [d6857, h 182 (by decide), agree6608 p q h, agree6652 p q h]
theorem nonnegative6857 (p : Pattern) : 0 ≤ d6857 p :=
  nonnegative_ite (p 182) (nonnegative6608 p) (nonnegative6652 p)
def d6858 (p : Pattern) : Int := if p 163 then d6857 p else d6687 p
theorem agree6858 (p q : Pattern) (h : Agree support p q) : d6858 p = d6858 q := by
  simp only [d6858, h 163 (by decide), agree6857 p q h, agree6687 p q h]
theorem nonnegative6858 (p : Pattern) : 0 ≤ d6858 p :=
  nonnegative_ite (p 163) (nonnegative6857 p) (nonnegative6687 p)
def d6859 (p : Pattern) : Int := if p 182 then d6613 p else d6652 p
theorem agree6859 (p q : Pattern) (h : Agree support p q) : d6859 p = d6859 q := by
  simp only [d6859, h 182 (by decide), agree6613 p q h, agree6652 p q h]
theorem nonnegative6859 (p : Pattern) : 0 ≤ d6859 p :=
  nonnegative_ite (p 182) (nonnegative6613 p) (nonnegative6652 p)
def d6860 (p : Pattern) : Int := if p 182 then d12 p else d6688 p
theorem agree6860 (p q : Pattern) (h : Agree support p q) : d6860 p = d6860 q := by
  simp only [d6860, h 182 (by decide), agree12 p q h, agree6688 p q h]
theorem nonnegative6860 (p : Pattern) : 0 ≤ d6860 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6688 p)
def d6861 (p : Pattern) : Int := if p 163 then d6860 p else d6859 p
theorem agree6861 (p q : Pattern) (h : Agree support p q) : d6861 p = d6861 q := by
  simp only [d6861, h 163 (by decide), agree6860 p q h, agree6859 p q h]
theorem nonnegative6861 (p : Pattern) : 0 ≤ d6861 p :=
  nonnegative_ite (p 163) (nonnegative6860 p) (nonnegative6859 p)
def d6862 (p : Pattern) : Int := if p 162 then d6861 p else d6858 p
theorem agree6862 (p q : Pattern) (h : Agree support p q) : d6862 p = d6862 q := by
  simp only [d6862, h 162 (by decide), agree6861 p q h, agree6858 p q h]
theorem nonnegative6862 (p : Pattern) : 0 ≤ d6862 p :=
  nonnegative_ite (p 162) (nonnegative6861 p) (nonnegative6858 p)
def d6863 (p : Pattern) : Int := if p 163 then d6860 p else d6653 p
theorem agree6863 (p q : Pattern) (h : Agree support p q) : d6863 p = d6863 q := by
  simp only [d6863, h 163 (by decide), agree6860 p q h, agree6653 p q h]
theorem nonnegative6863 (p : Pattern) : 0 ≤ d6863 p :=
  nonnegative_ite (p 163) (nonnegative6860 p) (nonnegative6653 p)
def d6864 (p : Pattern) : Int := if p 162 then d6660 p else d6863 p
theorem agree6864 (p q : Pattern) (h : Agree support p q) : d6864 p = d6864 q := by
  simp only [d6864, h 162 (by decide), agree6660 p q h, agree6863 p q h]
theorem nonnegative6864 (p : Pattern) : 0 ≤ d6864 p :=
  nonnegative_ite (p 162) (nonnegative6660 p) (nonnegative6863 p)
def d6865 (p : Pattern) : Int := if p 161 then d6864 p else d6862 p
theorem agree6865 (p q : Pattern) (h : Agree support p q) : d6865 p = d6865 q := by
  simp only [d6865, h 161 (by decide), agree6864 p q h, agree6862 p q h]
theorem nonnegative6865 (p : Pattern) : 0 ≤ d6865 p :=
  nonnegative_ite (p 161) (nonnegative6864 p) (nonnegative6862 p)
def d6866 (p : Pattern) : Int := if p 160 then d6865 p else d6856 p
theorem agree6866 (p q : Pattern) (h : Agree support p q) : d6866 p = d6866 q := by
  simp only [d6866, h 160 (by decide), agree6865 p q h, agree6856 p q h]
theorem nonnegative6866 (p : Pattern) : 0 ≤ d6866 p :=
  nonnegative_ite (p 160) (nonnegative6865 p) (nonnegative6856 p)
def d6867 (p : Pattern) : Int := if p 225 then d6596 p else d6598 p
theorem agree6867 (p q : Pattern) (h : Agree support p q) : d6867 p = d6867 q := by
  simp only [d6867, h 225 (by decide), agree6596 p q h, agree6598 p q h]
theorem nonnegative6867 (p : Pattern) : 0 ≤ d6867 p :=
  nonnegative_ite (p 225) (nonnegative6596 p) (nonnegative6598 p)
def d6868 (p : Pattern) : Int := if p 224 then d6867 p else d6597 p
theorem agree6868 (p q : Pattern) (h : Agree support p q) : d6868 p = d6868 q := by
  simp only [d6868, h 224 (by decide), agree6867 p q h, agree6597 p q h]
theorem nonnegative6868 (p : Pattern) : 0 ≤ d6868 p :=
  nonnegative_ite (p 224) (nonnegative6867 p) (nonnegative6597 p)
def d6869 (p : Pattern) : Int := if p 204 then d6868 p else d2 p
theorem agree6869 (p q : Pattern) (h : Agree support p q) : d6869 p = d6869 q := by
  simp only [d6869, h 204 (by decide), agree6868 p q h, agree2 p q h]
theorem nonnegative6869 (p : Pattern) : 0 ≤ d6869 p :=
  nonnegative_ite (p 204) (nonnegative6868 p) (nonnegative2 p)
def d6870 (p : Pattern) : Int := if p 204 then d12 p else d6631 p
theorem agree6870 (p q : Pattern) (h : Agree support p q) : d6870 p = d6870 q := by
  simp only [d6870, h 204 (by decide), agree12 p q h, agree6631 p q h]
theorem nonnegative6870 (p : Pattern) : 0 ≤ d6870 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6631 p)
def d6871 (p : Pattern) : Int := if p 182 then d6870 p else d6869 p
theorem agree6871 (p q : Pattern) (h : Agree support p q) : d6871 p = d6871 q := by
  simp only [d6871, h 182 (by decide), agree6870 p q h, agree6869 p q h]
theorem nonnegative6871 (p : Pattern) : 0 ≤ d6871 p :=
  nonnegative_ite (p 182) (nonnegative6870 p) (nonnegative6869 p)
def d6872 (p : Pattern) : Int := if p 163 then d6871 p else d6669 p
theorem agree6872 (p q : Pattern) (h : Agree support p q) : d6872 p = d6872 q := by
  simp only [d6872, h 163 (by decide), agree6871 p q h, agree6669 p q h]
theorem nonnegative6872 (p : Pattern) : 0 ≤ d6872 p :=
  nonnegative_ite (p 163) (nonnegative6871 p) (nonnegative6669 p)
def d6873 (p : Pattern) : Int := if p 163 then d6683 p else d6852 p
theorem agree6873 (p q : Pattern) (h : Agree support p q) : d6873 p = d6873 q := by
  simp only [d6873, h 163 (by decide), agree6683 p q h, agree6852 p q h]
theorem nonnegative6873 (p : Pattern) : 0 ≤ d6873 p :=
  nonnegative_ite (p 163) (nonnegative6683 p) (nonnegative6852 p)
def d6874 (p : Pattern) : Int := if p 162 then d6873 p else d6872 p
theorem agree6874 (p q : Pattern) (h : Agree support p q) : d6874 p = d6874 q := by
  simp only [d6874, h 162 (by decide), agree6873 p q h, agree6872 p q h]
theorem nonnegative6874 (p : Pattern) : 0 ≤ d6874 p :=
  nonnegative_ite (p 162) (nonnegative6873 p) (nonnegative6872 p)
def d6875 (p : Pattern) : Int := if p 163 then d6645 p else d6852 p
theorem agree6875 (p q : Pattern) (h : Agree support p q) : d6875 p = d6875 q := by
  simp only [d6875, h 163 (by decide), agree6645 p q h, agree6852 p q h]
theorem nonnegative6875 (p : Pattern) : 0 ≤ d6875 p :=
  nonnegative_ite (p 163) (nonnegative6645 p) (nonnegative6852 p)
def d6876 (p : Pattern) : Int := if p 162 then d6649 p else d6875 p
theorem agree6876 (p q : Pattern) (h : Agree support p q) : d6876 p = d6876 q := by
  simp only [d6876, h 162 (by decide), agree6649 p q h, agree6875 p q h]
theorem nonnegative6876 (p : Pattern) : 0 ≤ d6876 p :=
  nonnegative_ite (p 162) (nonnegative6649 p) (nonnegative6875 p)
def d6877 (p : Pattern) : Int := if p 161 then d6876 p else d6874 p
theorem agree6877 (p q : Pattern) (h : Agree support p q) : d6877 p = d6877 q := by
  simp only [d6877, h 161 (by decide), agree6876 p q h, agree6874 p q h]
theorem nonnegative6877 (p : Pattern) : 0 ≤ d6877 p :=
  nonnegative_ite (p 161) (nonnegative6876 p) (nonnegative6874 p)
def d6878 (p : Pattern) : Int := if p 163 then d6620 p else d6857 p
theorem agree6878 (p q : Pattern) (h : Agree support p q) : d6878 p = d6878 q := by
  simp only [d6878, h 163 (by decide), agree6620 p q h, agree6857 p q h]
theorem nonnegative6878 (p : Pattern) : 0 ≤ d6878 p :=
  nonnegative_ite (p 163) (nonnegative6620 p) (nonnegative6857 p)
def d6879 (p : Pattern) : Int := if p 163 then d6659 p else d6860 p
theorem agree6879 (p q : Pattern) (h : Agree support p q) : d6879 p = d6879 q := by
  simp only [d6879, h 163 (by decide), agree6659 p q h, agree6860 p q h]
theorem nonnegative6879 (p : Pattern) : 0 ≤ d6879 p :=
  nonnegative_ite (p 163) (nonnegative6659 p) (nonnegative6860 p)
def d6880 (p : Pattern) : Int := if p 162 then d6879 p else d6878 p
theorem agree6880 (p q : Pattern) (h : Agree support p q) : d6880 p = d6880 q := by
  simp only [d6880, h 162 (by decide), agree6879 p q h, agree6878 p q h]
theorem nonnegative6880 (p : Pattern) : 0 ≤ d6880 p :=
  nonnegative_ite (p 162) (nonnegative6879 p) (nonnegative6878 p)
def d6881 (p : Pattern) : Int := if p 163 then d12 p else d6860 p
theorem agree6881 (p q : Pattern) (h : Agree support p q) : d6881 p = d6881 q := by
  simp only [d6881, h 163 (by decide), agree12 p q h, agree6860 p q h]
theorem nonnegative6881 (p : Pattern) : 0 ≤ d6881 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6860 p)
def d6882 (p : Pattern) : Int := if p 162 then d12 p else d6881 p
theorem agree6882 (p q : Pattern) (h : Agree support p q) : d6882 p = d6882 q := by
  simp only [d6882, h 162 (by decide), agree12 p q h, agree6881 p q h]
theorem nonnegative6882 (p : Pattern) : 0 ≤ d6882 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6881 p)
def d6883 (p : Pattern) : Int := if p 161 then d6882 p else d6880 p
theorem agree6883 (p q : Pattern) (h : Agree support p q) : d6883 p = d6883 q := by
  simp only [d6883, h 161 (by decide), agree6882 p q h, agree6880 p q h]
theorem nonnegative6883 (p : Pattern) : 0 ≤ d6883 p :=
  nonnegative_ite (p 161) (nonnegative6882 p) (nonnegative6880 p)
def d6884 (p : Pattern) : Int := if p 160 then d6883 p else d6877 p
theorem agree6884 (p q : Pattern) (h : Agree support p q) : d6884 p = d6884 q := by
  simp only [d6884, h 160 (by decide), agree6883 p q h, agree6877 p q h]
theorem nonnegative6884 (p : Pattern) : 0 ≤ d6884 p :=
  nonnegative_ite (p 160) (nonnegative6883 p) (nonnegative6877 p)
def d6885 (p : Pattern) : Int := if p 141 then d6884 p else d6866 p
theorem agree6885 (p q : Pattern) (h : Agree support p q) : d6885 p = d6885 q := by
  simp only [d6885, h 141 (by decide), agree6884 p q h, agree6866 p q h]
theorem nonnegative6885 (p : Pattern) : 0 ≤ d6885 p :=
  nonnegative_ite (p 141) (nonnegative6884 p) (nonnegative6866 p)
def d6886 (p : Pattern) : Int := if p 204 then d6672 p else d0 p
theorem agree6886 (p q : Pattern) (h : Agree support p q) : d6886 p = d6886 q := by
  simp only [d6886, h 204 (by decide), agree6672 p q h, agree0 p q h]
theorem nonnegative6886 (p : Pattern) : 0 ≤ d6886 p :=
  nonnegative_ite (p 204) (nonnegative6672 p) (nonnegative0 p)
def d6887 (p : Pattern) : Int := if p 204 then d12 p else d6666 p
theorem agree6887 (p q : Pattern) (h : Agree support p q) : d6887 p = d6887 q := by
  simp only [d6887, h 204 (by decide), agree12 p q h, agree6666 p q h]
theorem nonnegative6887 (p : Pattern) : 0 ≤ d6887 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6666 p)
def d6888 (p : Pattern) : Int := if p 182 then d6887 p else d6886 p
theorem agree6888 (p q : Pattern) (h : Agree support p q) : d6888 p = d6888 q := by
  simp only [d6888, h 182 (by decide), agree6887 p q h, agree6886 p q h]
theorem nonnegative6888 (p : Pattern) : 0 ≤ d6888 p :=
  nonnegative_ite (p 182) (nonnegative6887 p) (nonnegative6886 p)
def d6889 (p : Pattern) : Int := if p 163 then d6677 p else d6888 p
theorem agree6889 (p q : Pattern) (h : Agree support p q) : d6889 p = d6889 q := by
  simp only [d6889, h 163 (by decide), agree6677 p q h, agree6888 p q h]
theorem nonnegative6889 (p : Pattern) : 0 ≤ d6889 p :=
  nonnegative_ite (p 163) (nonnegative6677 p) (nonnegative6888 p)
def d6890 (p : Pattern) : Int := if p 162 then d6690 p else d6889 p
theorem agree6890 (p q : Pattern) (h : Agree support p q) : d6890 p = d6890 q := by
  simp only [d6890, h 162 (by decide), agree6690 p q h, agree6889 p q h]
theorem nonnegative6890 (p : Pattern) : 0 ≤ d6890 p :=
  nonnegative_ite (p 162) (nonnegative6690 p) (nonnegative6889 p)
def d6891 (p : Pattern) : Int := if p 161 then d6691 p else d6890 p
theorem agree6891 (p q : Pattern) (h : Agree support p q) : d6891 p = d6891 q := by
  simp only [d6891, h 161 (by decide), agree6691 p q h, agree6890 p q h]
theorem nonnegative6891 (p : Pattern) : 0 ≤ d6891 p :=
  nonnegative_ite (p 161) (nonnegative6691 p) (nonnegative6890 p)
def d6892 (p : Pattern) : Int := if p 225 then d3461 p else d8 p
theorem agree6892 (p q : Pattern) (h : Agree support p q) : d6892 p = d6892 q := by
  simp only [d6892, h 225 (by decide), agree3461 p q h, agree8 p q h]
theorem nonnegative6892 (p : Pattern) : 0 ≤ d6892 p :=
  nonnegative_ite (p 225) (nonnegative3461 p) (nonnegative8 p)
def d6893 (p : Pattern) : Int := if p 224 then d3461 p else d6892 p
theorem agree6893 (p q : Pattern) (h : Agree support p q) : d6893 p = d6893 q := by
  simp only [d6893, h 224 (by decide), agree3461 p q h, agree6892 p q h]
theorem nonnegative6893 (p : Pattern) : 0 ≤ d6893 p :=
  nonnegative_ite (p 224) (nonnegative3461 p) (nonnegative6892 p)
def d6894 (p : Pattern) : Int := if p 204 then d6893 p else d8 p
theorem agree6894 (p q : Pattern) (h : Agree support p q) : d6894 p = d6894 q := by
  simp only [d6894, h 204 (by decide), agree6893 p q h, agree8 p q h]
theorem nonnegative6894 (p : Pattern) : 0 ≤ d6894 p :=
  nonnegative_ite (p 204) (nonnegative6893 p) (nonnegative8 p)
def d6895 (p : Pattern) : Int := if p 204 then d12 p else d6893 p
theorem agree6895 (p q : Pattern) (h : Agree support p q) : d6895 p = d6895 q := by
  simp only [d6895, h 204 (by decide), agree12 p q h, agree6893 p q h]
theorem nonnegative6895 (p : Pattern) : 0 ≤ d6895 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6893 p)
def d6896 (p : Pattern) : Int := if p 182 then d6895 p else d6894 p
theorem agree6896 (p q : Pattern) (h : Agree support p q) : d6896 p = d6896 q := by
  simp only [d6896, h 182 (by decide), agree6895 p q h, agree6894 p q h]
theorem nonnegative6896 (p : Pattern) : 0 ≤ d6896 p :=
  nonnegative_ite (p 182) (nonnegative6895 p) (nonnegative6894 p)
def d6897 (p : Pattern) : Int := if p 163 then d6896 p else d6679 p
theorem agree6897 (p q : Pattern) (h : Agree support p q) : d6897 p = d6897 q := by
  simp only [d6897, h 163 (by decide), agree6896 p q h, agree6679 p q h]
theorem nonnegative6897 (p : Pattern) : 0 ≤ d6897 p :=
  nonnegative_ite (p 163) (nonnegative6896 p) (nonnegative6679 p)
def d6898 (p : Pattern) : Int := if p 162 then d12 p else d6897 p
theorem agree6898 (p q : Pattern) (h : Agree support p q) : d6898 p = d6898 q := by
  simp only [d6898, h 162 (by decide), agree12 p q h, agree6897 p q h]
theorem nonnegative6898 (p : Pattern) : 0 ≤ d6898 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6897 p)
def d6899 (p : Pattern) : Int := if p 161 then d12 p else d6898 p
theorem agree6899 (p q : Pattern) (h : Agree support p q) : d6899 p = d6899 q := by
  simp only [d6899, h 161 (by decide), agree12 p q h, agree6898 p q h]
theorem nonnegative6899 (p : Pattern) : 0 ≤ d6899 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6898 p)
def d6900 (p : Pattern) : Int := if p 160 then d6899 p else d6891 p
theorem agree6900 (p q : Pattern) (h : Agree support p q) : d6900 p = d6900 q := by
  simp only [d6900, h 160 (by decide), agree6899 p q h, agree6891 p q h]
theorem nonnegative6900 (p : Pattern) : 0 ≤ d6900 p :=
  nonnegative_ite (p 160) (nonnegative6899 p) (nonnegative6891 p)
def d6901 (p : Pattern) : Int := if p 246 then d10 p else d2 p
theorem agree6901 (p q : Pattern) (h : Agree support p q) : d6901 p = d6901 q := by
  simp only [d6901, h 246 (by decide), agree10 p q h, agree2 p q h]
theorem nonnegative6901 (p : Pattern) : 0 ≤ d6901 p :=
  nonnegative_ite (p 246) (nonnegative10 p) (nonnegative2 p)
def d6902 (p : Pattern) : Int := if p 225 then d6901 p else d6598 p
theorem agree6902 (p q : Pattern) (h : Agree support p q) : d6902 p = d6902 q := by
  simp only [d6902, h 225 (by decide), agree6901 p q h, agree6598 p q h]
theorem nonnegative6902 (p : Pattern) : 0 ≤ d6902 p :=
  nonnegative_ite (p 225) (nonnegative6901 p) (nonnegative6598 p)
def d6903 (p : Pattern) : Int := if p 224 then d6902 p else d6597 p
theorem agree6903 (p q : Pattern) (h : Agree support p q) : d6903 p = d6903 q := by
  simp only [d6903, h 224 (by decide), agree6902 p q h, agree6597 p q h]
theorem nonnegative6903 (p : Pattern) : 0 ≤ d6903 p :=
  nonnegative_ite (p 224) (nonnegative6902 p) (nonnegative6597 p)
def d6904 (p : Pattern) : Int := if p 204 then d12 p else d6903 p
theorem agree6904 (p q : Pattern) (h : Agree support p q) : d6904 p = d6904 q := by
  simp only [d6904, h 204 (by decide), agree12 p q h, agree6903 p q h]
theorem nonnegative6904 (p : Pattern) : 0 ≤ d6904 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6903 p)
def d6905 (p : Pattern) : Int := if p 182 then d6904 p else d6652 p
theorem agree6905 (p q : Pattern) (h : Agree support p q) : d6905 p = d6905 q := by
  simp only [d6905, h 182 (by decide), agree6904 p q h, agree6652 p q h]
theorem nonnegative6905 (p : Pattern) : 0 ≤ d6905 p :=
  nonnegative_ite (p 182) (nonnegative6904 p) (nonnegative6652 p)
def d6906 (p : Pattern) : Int := if p 163 then d6687 p else d6905 p
theorem agree6906 (p q : Pattern) (h : Agree support p q) : d6906 p = d6906 q := by
  simp only [d6906, h 163 (by decide), agree6687 p q h, agree6905 p q h]
theorem nonnegative6906 (p : Pattern) : 0 ≤ d6906 p :=
  nonnegative_ite (p 163) (nonnegative6687 p) (nonnegative6905 p)
def d6907 (p : Pattern) : Int := if p 163 then d6648 p else d6679 p
theorem agree6907 (p q : Pattern) (h : Agree support p q) : d6907 p = d6907 q := by
  simp only [d6907, h 163 (by decide), agree6648 p q h, agree6679 p q h]
theorem nonnegative6907 (p : Pattern) : 0 ≤ d6907 p :=
  nonnegative_ite (p 163) (nonnegative6648 p) (nonnegative6679 p)
def d6908 (p : Pattern) : Int := if p 162 then d6907 p else d6906 p
theorem agree6908 (p q : Pattern) (h : Agree support p q) : d6908 p = d6908 q := by
  simp only [d6908, h 162 (by decide), agree6907 p q h, agree6906 p q h]
theorem nonnegative6908 (p : Pattern) : 0 ≤ d6908 p :=
  nonnegative_ite (p 162) (nonnegative6907 p) (nonnegative6906 p)
def d6909 (p : Pattern) : Int := if p 161 then d6701 p else d6908 p
theorem agree6909 (p q : Pattern) (h : Agree support p q) : d6909 p = d6909 q := by
  simp only [d6909, h 161 (by decide), agree6701 p q h, agree6908 p q h]
theorem nonnegative6909 (p : Pattern) : 0 ≤ d6909 p :=
  nonnegative_ite (p 161) (nonnegative6701 p) (nonnegative6908 p)
def d6910 (p : Pattern) : Int := if p 163 then d12 p else d6896 p
theorem agree6910 (p q : Pattern) (h : Agree support p q) : d6910 p = d6910 q := by
  simp only [d6910, h 163 (by decide), agree12 p q h, agree6896 p q h]
theorem nonnegative6910 (p : Pattern) : 0 ≤ d6910 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6896 p)
def d6911 (p : Pattern) : Int := if p 162 then d12 p else d6910 p
theorem agree6911 (p q : Pattern) (h : Agree support p q) : d6911 p = d6911 q := by
  simp only [d6911, h 162 (by decide), agree12 p q h, agree6910 p q h]
theorem nonnegative6911 (p : Pattern) : 0 ≤ d6911 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6910 p)
def d6912 (p : Pattern) : Int := if p 161 then d12 p else d6911 p
theorem agree6912 (p q : Pattern) (h : Agree support p q) : d6912 p = d6912 q := by
  simp only [d6912, h 161 (by decide), agree12 p q h, agree6911 p q h]
theorem nonnegative6912 (p : Pattern) : 0 ≤ d6912 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6911 p)
def d6913 (p : Pattern) : Int := if p 160 then d6912 p else d6909 p
theorem agree6913 (p q : Pattern) (h : Agree support p q) : d6913 p = d6913 q := by
  simp only [d6913, h 160 (by decide), agree6912 p q h, agree6909 p q h]
theorem nonnegative6913 (p : Pattern) : 0 ≤ d6913 p :=
  nonnegative_ite (p 160) (nonnegative6912 p) (nonnegative6909 p)
def d6914 (p : Pattern) : Int := if p 141 then d6913 p else d6900 p
theorem agree6914 (p q : Pattern) (h : Agree support p q) : d6914 p = d6914 q := by
  simp only [d6914, h 141 (by decide), agree6913 p q h, agree6900 p q h]
theorem nonnegative6914 (p : Pattern) : 0 ≤ d6914 p :=
  nonnegative_ite (p 141) (nonnegative6913 p) (nonnegative6900 p)
def d6915 (p : Pattern) : Int := if p 138 then d6914 p else d6885 p
theorem agree6915 (p q : Pattern) (h : Agree support p q) : d6915 p = d6915 q := by
  simp only [d6915, h 138 (by decide), agree6914 p q h, agree6885 p q h]
theorem nonnegative6915 (p : Pattern) : 0 ≤ d6915 p :=
  nonnegative_ite (p 138) (nonnegative6914 p) (nonnegative6885 p)
def d6916 (p : Pattern) : Int := if p 138 then d12 p else d6914 p
theorem agree6916 (p q : Pattern) (h : Agree support p q) : d6916 p = d6916 q := by
  simp only [d6916, h 138 (by decide), agree12 p q h, agree6914 p q h]
theorem nonnegative6916 (p : Pattern) : 0 ≤ d6916 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6914 p)
def d6917 (p : Pattern) : Int := if p 116 then d6916 p else d6915 p
theorem agree6917 (p q : Pattern) (h : Agree support p q) : d6917 p = d6917 q := by
  simp only [d6917, h 116 (by decide), agree6916 p q h, agree6915 p q h]
theorem nonnegative6917 (p : Pattern) : 0 ≤ d6917 p :=
  nonnegative_ite (p 116) (nonnegative6916 p) (nonnegative6915 p)
def d6918 (p : Pattern) : Int := if p 115 then d6917 p else d6715 p
theorem agree6918 (p q : Pattern) (h : Agree support p q) : d6918 p = d6918 q := by
  simp only [d6918, h 115 (by decide), agree6917 p q h, agree6715 p q h]
theorem nonnegative6918 (p : Pattern) : 0 ≤ d6918 p :=
  nonnegative_ite (p 115) (nonnegative6917 p) (nonnegative6715 p)
def d6919 (p : Pattern) : Int := if p 71 then d6918 p else d6718 p
theorem agree6919 (p q : Pattern) (h : Agree support p q) : d6919 p = d6919 q := by
  simp only [d6919, h 71 (by decide), agree6918 p q h, agree6718 p q h]
theorem nonnegative6919 (p : Pattern) : 0 ≤ d6919 p :=
  nonnegative_ite (p 71) (nonnegative6918 p) (nonnegative6718 p)
def d6920 (p : Pattern) : Int := if p 163 then d12 p else d6736 p
theorem agree6920 (p q : Pattern) (h : Agree support p q) : d6920 p = d6920 q := by
  simp only [d6920, h 163 (by decide), agree12 p q h, agree6736 p q h]
theorem nonnegative6920 (p : Pattern) : 0 ≤ d6920 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6736 p)
def d6921 (p : Pattern) : Int := if p 162 then d6920 p else d6783 p
theorem agree6921 (p q : Pattern) (h : Agree support p q) : d6921 p = d6921 q := by
  simp only [d6921, h 162 (by decide), agree6920 p q h, agree6783 p q h]
theorem nonnegative6921 (p : Pattern) : 0 ≤ d6921 p :=
  nonnegative_ite (p 162) (nonnegative6920 p) (nonnegative6783 p)
def d6922 (p : Pattern) : Int := if p 162 then d12 p else d6920 p
theorem agree6922 (p q : Pattern) (h : Agree support p q) : d6922 p = d6922 q := by
  simp only [d6922, h 162 (by decide), agree12 p q h, agree6920 p q h]
theorem nonnegative6922 (p : Pattern) : 0 ≤ d6922 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6920 p)
def d6923 (p : Pattern) : Int := if p 161 then d6922 p else d6921 p
theorem agree6923 (p q : Pattern) (h : Agree support p q) : d6923 p = d6923 q := by
  simp only [d6923, h 161 (by decide), agree6922 p q h, agree6921 p q h]
theorem nonnegative6923 (p : Pattern) : 0 ≤ d6923 p :=
  nonnegative_ite (p 161) (nonnegative6922 p) (nonnegative6921 p)
def d6924 (p : Pattern) : Int := if p 163 then d12 p else d6768 p
theorem agree6924 (p q : Pattern) (h : Agree support p q) : d6924 p = d6924 q := by
  simp only [d6924, h 163 (by decide), agree12 p q h, agree6768 p q h]
theorem nonnegative6924 (p : Pattern) : 0 ≤ d6924 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6768 p)
def d6925 (p : Pattern) : Int := if p 162 then d6924 p else d6791 p
theorem agree6925 (p q : Pattern) (h : Agree support p q) : d6925 p = d6925 q := by
  simp only [d6925, h 162 (by decide), agree6924 p q h, agree6791 p q h]
theorem nonnegative6925 (p : Pattern) : 0 ≤ d6925 p :=
  nonnegative_ite (p 162) (nonnegative6924 p) (nonnegative6791 p)
def d6926 (p : Pattern) : Int := if p 162 then d12 p else d6924 p
theorem agree6926 (p q : Pattern) (h : Agree support p q) : d6926 p = d6926 q := by
  simp only [d6926, h 162 (by decide), agree12 p q h, agree6924 p q h]
theorem nonnegative6926 (p : Pattern) : 0 ≤ d6926 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6924 p)
def d6927 (p : Pattern) : Int := if p 161 then d6926 p else d6925 p
theorem agree6927 (p q : Pattern) (h : Agree support p q) : d6927 p = d6927 q := by
  simp only [d6927, h 161 (by decide), agree6926 p q h, agree6925 p q h]
theorem nonnegative6927 (p : Pattern) : 0 ≤ d6927 p :=
  nonnegative_ite (p 161) (nonnegative6926 p) (nonnegative6925 p)
def d6928 (p : Pattern) : Int := if p 160 then d6927 p else d6923 p
theorem agree6928 (p q : Pattern) (h : Agree support p q) : d6928 p = d6928 q := by
  simp only [d6928, h 160 (by decide), agree6927 p q h, agree6923 p q h]
theorem nonnegative6928 (p : Pattern) : 0 ≤ d6928 p :=
  nonnegative_ite (p 160) (nonnegative6927 p) (nonnegative6923 p)
def d6929 (p : Pattern) : Int := if p 141 then d6928 p else d6774 p
theorem agree6929 (p q : Pattern) (h : Agree support p q) : d6929 p = d6929 q := by
  simp only [d6929, h 141 (by decide), agree6928 p q h, agree6774 p q h]
theorem nonnegative6929 (p : Pattern) : 0 ≤ d6929 p :=
  nonnegative_ite (p 141) (nonnegative6928 p) (nonnegative6774 p)
def d6930 (p : Pattern) : Int := if p 163 then d12 p else d6813 p
theorem agree6930 (p q : Pattern) (h : Agree support p q) : d6930 p = d6930 q := by
  simp only [d6930, h 163 (by decide), agree12 p q h, agree6813 p q h]
theorem nonnegative6930 (p : Pattern) : 0 ≤ d6930 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6813 p)
def d6931 (p : Pattern) : Int := if p 162 then d6930 p else d6825 p
theorem agree6931 (p q : Pattern) (h : Agree support p q) : d6931 p = d6931 q := by
  simp only [d6931, h 162 (by decide), agree6930 p q h, agree6825 p q h]
theorem nonnegative6931 (p : Pattern) : 0 ≤ d6931 p :=
  nonnegative_ite (p 162) (nonnegative6930 p) (nonnegative6825 p)
def d6932 (p : Pattern) : Int := if p 162 then d12 p else d6930 p
theorem agree6932 (p q : Pattern) (h : Agree support p q) : d6932 p = d6932 q := by
  simp only [d6932, h 162 (by decide), agree12 p q h, agree6930 p q h]
theorem nonnegative6932 (p : Pattern) : 0 ≤ d6932 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6930 p)
def d6933 (p : Pattern) : Int := if p 161 then d6932 p else d6931 p
theorem agree6933 (p q : Pattern) (h : Agree support p q) : d6933 p = d6933 q := by
  simp only [d6933, h 161 (by decide), agree6932 p q h, agree6931 p q h]
theorem nonnegative6933 (p : Pattern) : 0 ≤ d6933 p :=
  nonnegative_ite (p 161) (nonnegative6932 p) (nonnegative6931 p)
def d6934 (p : Pattern) : Int := if p 160 then d6833 p else d6933 p
theorem agree6934 (p q : Pattern) (h : Agree support p q) : d6934 p = d6934 q := by
  simp only [d6934, h 160 (by decide), agree6833 p q h, agree6933 p q h]
theorem nonnegative6934 (p : Pattern) : 0 ≤ d6934 p :=
  nonnegative_ite (p 160) (nonnegative6833 p) (nonnegative6933 p)
def d6935 (p : Pattern) : Int := if p 141 then d6934 p else d6824 p
theorem agree6935 (p q : Pattern) (h : Agree support p q) : d6935 p = d6935 q := by
  simp only [d6935, h 141 (by decide), agree6934 p q h, agree6824 p q h]
theorem nonnegative6935 (p : Pattern) : 0 ≤ d6935 p :=
  nonnegative_ite (p 141) (nonnegative6934 p) (nonnegative6824 p)
def d6936 (p : Pattern) : Int := if p 138 then d6935 p else d6929 p
theorem agree6936 (p q : Pattern) (h : Agree support p q) : d6936 p = d6936 q := by
  simp only [d6936, h 138 (by decide), agree6935 p q h, agree6929 p q h]
theorem nonnegative6936 (p : Pattern) : 0 ≤ d6936 p :=
  nonnegative_ite (p 138) (nonnegative6935 p) (nonnegative6929 p)
def d6937 (p : Pattern) : Int := if p 138 then d6840 p else d6935 p
theorem agree6937 (p q : Pattern) (h : Agree support p q) : d6937 p = d6937 q := by
  simp only [d6937, h 138 (by decide), agree6840 p q h, agree6935 p q h]
theorem nonnegative6937 (p : Pattern) : 0 ≤ d6937 p :=
  nonnegative_ite (p 138) (nonnegative6840 p) (nonnegative6935 p)
def d6938 (p : Pattern) : Int := if p 116 then d6937 p else d6936 p
theorem agree6938 (p q : Pattern) (h : Agree support p q) : d6938 p = d6938 q := by
  simp only [d6938, h 116 (by decide), agree6937 p q h, agree6936 p q h]
theorem nonnegative6938 (p : Pattern) : 0 ≤ d6938 p :=
  nonnegative_ite (p 116) (nonnegative6937 p) (nonnegative6936 p)
def d6939 (p : Pattern) : Int := if p 204 then d6806 p else d1 p
theorem agree6939 (p q : Pattern) (h : Agree support p q) : d6939 p = d6939 q := by
  simp only [d6939, h 204 (by decide), agree6806 p q h, agree1 p q h]
theorem nonnegative6939 (p : Pattern) : 0 ≤ d6939 p :=
  nonnegative_ite (p 204) (nonnegative6806 p) (nonnegative1 p)
def d6940 (p : Pattern) : Int := if p 204 then d12 p else d6800 p
theorem agree6940 (p q : Pattern) (h : Agree support p q) : d6940 p = d6940 q := by
  simp only [d6940, h 204 (by decide), agree12 p q h, agree6800 p q h]
theorem nonnegative6940 (p : Pattern) : 0 ≤ d6940 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6800 p)
def d6941 (p : Pattern) : Int := if p 182 then d6940 p else d6939 p
theorem agree6941 (p q : Pattern) (h : Agree support p q) : d6941 p = d6941 q := by
  simp only [d6941, h 182 (by decide), agree6940 p q h, agree6939 p q h]
theorem nonnegative6941 (p : Pattern) : 0 ≤ d6941 p :=
  nonnegative_ite (p 182) (nonnegative6940 p) (nonnegative6939 p)
def d6942 (p : Pattern) : Int := if p 163 then d6813 p else d6941 p
theorem agree6942 (p q : Pattern) (h : Agree support p q) : d6942 p = d6942 q := by
  simp only [d6942, h 163 (by decide), agree6813 p q h, agree6941 p q h]
theorem nonnegative6942 (p : Pattern) : 0 ≤ d6942 p :=
  nonnegative_ite (p 163) (nonnegative6813 p) (nonnegative6941 p)
def d6943 (p : Pattern) : Int := if p 162 then d6942 p else d6803 p
theorem agree6943 (p q : Pattern) (h : Agree support p q) : d6943 p = d6943 q := by
  simp only [d6943, h 162 (by decide), agree6942 p q h, agree6803 p q h]
theorem nonnegative6943 (p : Pattern) : 0 ≤ d6943 p :=
  nonnegative_ite (p 162) (nonnegative6942 p) (nonnegative6803 p)
def d6944 (p : Pattern) : Int := if p 163 then d6813 p else d6808 p
theorem agree6944 (p q : Pattern) (h : Agree support p q) : d6944 p = d6944 q := by
  simp only [d6944, h 163 (by decide), agree6813 p q h, agree6808 p q h]
theorem nonnegative6944 (p : Pattern) : 0 ≤ d6944 p :=
  nonnegative_ite (p 163) (nonnegative6813 p) (nonnegative6808 p)
def d6945 (p : Pattern) : Int := if p 162 then d6739 p else d6944 p
theorem agree6945 (p q : Pattern) (h : Agree support p q) : d6945 p = d6945 q := by
  simp only [d6945, h 162 (by decide), agree6739 p q h, agree6944 p q h]
theorem nonnegative6945 (p : Pattern) : 0 ≤ d6945 p :=
  nonnegative_ite (p 162) (nonnegative6739 p) (nonnegative6944 p)
def d6946 (p : Pattern) : Int := if p 161 then d6945 p else d6943 p
theorem agree6946 (p q : Pattern) (h : Agree support p q) : d6946 p = d6946 q := by
  simp only [d6946, h 161 (by decide), agree6945 p q h, agree6943 p q h]
theorem nonnegative6946 (p : Pattern) : 0 ≤ d6946 p :=
  nonnegative_ite (p 161) (nonnegative6945 p) (nonnegative6943 p)
def d6947 (p : Pattern) : Int := if p 182 then d6759 p else d6789 p
theorem agree6947 (p q : Pattern) (h : Agree support p q) : d6947 p = d6947 q := by
  simp only [d6947, h 182 (by decide), agree6759 p q h, agree6789 p q h]
theorem nonnegative6947 (p : Pattern) : 0 ≤ d6947 p :=
  nonnegative_ite (p 182) (nonnegative6759 p) (nonnegative6789 p)
def d6948 (p : Pattern) : Int := if p 163 then d6947 p else d6818 p
theorem agree6948 (p q : Pattern) (h : Agree support p q) : d6948 p = d6948 q := by
  simp only [d6948, h 163 (by decide), agree6947 p q h, agree6818 p q h]
theorem nonnegative6948 (p : Pattern) : 0 ≤ d6948 p :=
  nonnegative_ite (p 163) (nonnegative6947 p) (nonnegative6818 p)
def d6949 (p : Pattern) : Int := if p 162 then d6924 p else d6948 p
theorem agree6949 (p q : Pattern) (h : Agree support p q) : d6949 p = d6949 q := by
  simp only [d6949, h 162 (by decide), agree6924 p q h, agree6948 p q h]
theorem nonnegative6949 (p : Pattern) : 0 ≤ d6949 p :=
  nonnegative_ite (p 162) (nonnegative6924 p) (nonnegative6948 p)
def d6950 (p : Pattern) : Int := if p 182 then d12 p else d6819 p
theorem agree6950 (p q : Pattern) (h : Agree support p q) : d6950 p = d6950 q := by
  simp only [d6950, h 182 (by decide), agree12 p q h, agree6819 p q h]
theorem nonnegative6950 (p : Pattern) : 0 ≤ d6950 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6819 p)
def d6951 (p : Pattern) : Int := if p 163 then d12 p else d6950 p
theorem agree6951 (p q : Pattern) (h : Agree support p q) : d6951 p = d6951 q := by
  simp only [d6951, h 163 (by decide), agree12 p q h, agree6950 p q h]
theorem nonnegative6951 (p : Pattern) : 0 ≤ d6951 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6950 p)
def d6952 (p : Pattern) : Int := if p 162 then d12 p else d6951 p
theorem agree6952 (p q : Pattern) (h : Agree support p q) : d6952 p = d6952 q := by
  simp only [d6952, h 162 (by decide), agree12 p q h, agree6951 p q h]
theorem nonnegative6952 (p : Pattern) : 0 ≤ d6952 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6951 p)
def d6953 (p : Pattern) : Int := if p 161 then d6952 p else d6949 p
theorem agree6953 (p q : Pattern) (h : Agree support p q) : d6953 p = d6953 q := by
  simp only [d6953, h 161 (by decide), agree6952 p q h, agree6949 p q h]
theorem nonnegative6953 (p : Pattern) : 0 ≤ d6953 p :=
  nonnegative_ite (p 161) (nonnegative6952 p) (nonnegative6949 p)
def d6954 (p : Pattern) : Int := if p 160 then d6953 p else d6946 p
theorem agree6954 (p q : Pattern) (h : Agree support p q) : d6954 p = d6954 q := by
  simp only [d6954, h 160 (by decide), agree6953 p q h, agree6946 p q h]
theorem nonnegative6954 (p : Pattern) : 0 ≤ d6954 p :=
  nonnegative_ite (p 160) (nonnegative6953 p) (nonnegative6946 p)
def d6955 (p : Pattern) : Int := if p 225 then d6748 p else d6750 p
theorem agree6955 (p q : Pattern) (h : Agree support p q) : d6955 p = d6955 q := by
  simp only [d6955, h 225 (by decide), agree6748 p q h, agree6750 p q h]
theorem nonnegative6955 (p : Pattern) : 0 ≤ d6955 p :=
  nonnegative_ite (p 225) (nonnegative6748 p) (nonnegative6750 p)
def d6956 (p : Pattern) : Int := if p 224 then d6955 p else d6749 p
theorem agree6956 (p q : Pattern) (h : Agree support p q) : d6956 p = d6956 q := by
  simp only [d6956, h 224 (by decide), agree6955 p q h, agree6749 p q h]
theorem nonnegative6956 (p : Pattern) : 0 ≤ d6956 p :=
  nonnegative_ite (p 224) (nonnegative6955 p) (nonnegative6749 p)
def d6957 (p : Pattern) : Int := if p 204 then d6956 p else d3 p
theorem agree6957 (p q : Pattern) (h : Agree support p q) : d6957 p = d6957 q := by
  simp only [d6957, h 204 (by decide), agree6956 p q h, agree3 p q h]
theorem nonnegative6957 (p : Pattern) : 0 ≤ d6957 p :=
  nonnegative_ite (p 204) (nonnegative6956 p) (nonnegative3 p)
def d6958 (p : Pattern) : Int := if p 204 then d12 p else d6776 p
theorem agree6958 (p q : Pattern) (h : Agree support p q) : d6958 p = d6958 q := by
  simp only [d6958, h 204 (by decide), agree12 p q h, agree6776 p q h]
theorem nonnegative6958 (p : Pattern) : 0 ≤ d6958 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6776 p)
def d6959 (p : Pattern) : Int := if p 182 then d6958 p else d6957 p
theorem agree6959 (p q : Pattern) (h : Agree support p q) : d6959 p = d6959 q := by
  simp only [d6959, h 182 (by decide), agree6958 p q h, agree6957 p q h]
theorem nonnegative6959 (p : Pattern) : 0 ≤ d6959 p :=
  nonnegative_ite (p 182) (nonnegative6958 p) (nonnegative6957 p)
end NetHack.Sokoban22Refined85
