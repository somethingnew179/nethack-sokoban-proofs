/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes31
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3840 (p : Pattern) : Int := if p 163 then d3839 p else d3837 p
theorem agree3840 (p q : Pattern) (h : Agree support p q) : d3840 p = d3840 q := by
  simp only [d3840, h 163 (by decide), agree3839 p q h, agree3837 p q h]
theorem nonnegative3840 (p : Pattern) : 0 ≤ d3840 p :=
  nonnegative_ite (p 163) (nonnegative3839 p) (nonnegative3837 p)
def d3841 (p : Pattern) : Int := if p 162 then d12 p else d3840 p
theorem agree3841 (p q : Pattern) (h : Agree support p q) : d3841 p = d3841 q := by
  simp only [d3841, h 162 (by decide), agree12 p q h, agree3840 p q h]
theorem nonnegative3841 (p : Pattern) : 0 ≤ d3841 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3840 p)
def d3842 (p : Pattern) : Int := if p 161 then d12 p else d3841 p
theorem agree3842 (p q : Pattern) (h : Agree support p q) : d3842 p = d3842 q := by
  simp only [d3842, h 161 (by decide), agree12 p q h, agree3841 p q h]
theorem nonnegative3842 (p : Pattern) : 0 ≤ d3842 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3841 p)
def d3843 (p : Pattern) : Int := if p 160 then d3842 p else d3836 p
theorem agree3843 (p q : Pattern) (h : Agree support p q) : d3843 p = d3843 q := by
  simp only [d3843, h 160 (by decide), agree3842 p q h, agree3836 p q h]
theorem nonnegative3843 (p : Pattern) : 0 ≤ d3843 p :=
  nonnegative_ite (p 160) (nonnegative3842 p) (nonnegative3836 p)
def d3844 (p : Pattern) : Int := if p 163 then d3837 p else d3827 p
theorem agree3844 (p q : Pattern) (h : Agree support p q) : d3844 p = d3844 q := by
  simp only [d3844, h 163 (by decide), agree3837 p q h, agree3827 p q h]
theorem nonnegative3844 (p : Pattern) : 0 ≤ d3844 p :=
  nonnegative_ite (p 163) (nonnegative3837 p) (nonnegative3827 p)
def d3845 (p : Pattern) : Int := if p 163 then d3636 p else d3832 p
theorem agree3845 (p q : Pattern) (h : Agree support p q) : d3845 p = d3845 q := by
  simp only [d3845, h 163 (by decide), agree3636 p q h, agree3832 p q h]
theorem nonnegative3845 (p : Pattern) : 0 ≤ d3845 p :=
  nonnegative_ite (p 163) (nonnegative3636 p) (nonnegative3832 p)
def d3846 (p : Pattern) : Int := if p 162 then d3845 p else d3844 p
theorem agree3846 (p q : Pattern) (h : Agree support p q) : d3846 p = d3846 q := by
  simp only [d3846, h 162 (by decide), agree3845 p q h, agree3844 p q h]
theorem nonnegative3846 (p : Pattern) : 0 ≤ d3846 p :=
  nonnegative_ite (p 162) (nonnegative3845 p) (nonnegative3844 p)
def d3847 (p : Pattern) : Int := if p 163 then d3639 p else d3832 p
theorem agree3847 (p q : Pattern) (h : Agree support p q) : d3847 p = d3847 q := by
  simp only [d3847, h 163 (by decide), agree3639 p q h, agree3832 p q h]
theorem nonnegative3847 (p : Pattern) : 0 ≤ d3847 p :=
  nonnegative_ite (p 163) (nonnegative3639 p) (nonnegative3832 p)
def d3848 (p : Pattern) : Int := if p 162 then d12 p else d3847 p
theorem agree3848 (p q : Pattern) (h : Agree support p q) : d3848 p = d3848 q := by
  simp only [d3848, h 162 (by decide), agree12 p q h, agree3847 p q h]
theorem nonnegative3848 (p : Pattern) : 0 ≤ d3848 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3847 p)
def d3849 (p : Pattern) : Int := if p 161 then d3848 p else d3846 p
theorem agree3849 (p q : Pattern) (h : Agree support p q) : d3849 p = d3849 q := by
  simp only [d3849, h 161 (by decide), agree3848 p q h, agree3846 p q h]
theorem nonnegative3849 (p : Pattern) : 0 ≤ d3849 p :=
  nonnegative_ite (p 161) (nonnegative3848 p) (nonnegative3846 p)
def d3850 (p : Pattern) : Int := if p 163 then d12 p else d3839 p
theorem agree3850 (p q : Pattern) (h : Agree support p q) : d3850 p = d3850 q := by
  simp only [d3850, h 163 (by decide), agree12 p q h, agree3839 p q h]
theorem nonnegative3850 (p : Pattern) : 0 ≤ d3850 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3839 p)
def d3851 (p : Pattern) : Int := if p 162 then d12 p else d3850 p
theorem agree3851 (p q : Pattern) (h : Agree support p q) : d3851 p = d3851 q := by
  simp only [d3851, h 162 (by decide), agree12 p q h, agree3850 p q h]
theorem nonnegative3851 (p : Pattern) : 0 ≤ d3851 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3850 p)
def d3852 (p : Pattern) : Int := if p 161 then d12 p else d3851 p
theorem agree3852 (p q : Pattern) (h : Agree support p q) : d3852 p = d3852 q := by
  simp only [d3852, h 161 (by decide), agree12 p q h, agree3851 p q h]
theorem nonnegative3852 (p : Pattern) : 0 ≤ d3852 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3851 p)
def d3853 (p : Pattern) : Int := if p 160 then d3852 p else d3849 p
theorem agree3853 (p q : Pattern) (h : Agree support p q) : d3853 p = d3853 q := by
  simp only [d3853, h 160 (by decide), agree3852 p q h, agree3849 p q h]
theorem nonnegative3853 (p : Pattern) : 0 ≤ d3853 p :=
  nonnegative_ite (p 160) (nonnegative3852 p) (nonnegative3849 p)
def d3854 (p : Pattern) : Int := if p 141 then d3853 p else d3843 p
theorem agree3854 (p q : Pattern) (h : Agree support p q) : d3854 p = d3854 q := by
  simp only [d3854, h 141 (by decide), agree3853 p q h, agree3843 p q h]
theorem nonnegative3854 (p : Pattern) : 0 ≤ d3854 p :=
  nonnegative_ite (p 141) (nonnegative3853 p) (nonnegative3843 p)
def d3855 (p : Pattern) : Int := if p 138 then d3854 p else d3817 p
theorem agree3855 (p q : Pattern) (h : Agree support p q) : d3855 p = d3855 q := by
  simp only [d3855, h 138 (by decide), agree3854 p q h, agree3817 p q h]
theorem nonnegative3855 (p : Pattern) : 0 ≤ d3855 p :=
  nonnegative_ite (p 138) (nonnegative3854 p) (nonnegative3817 p)
def d3856 (p : Pattern) : Int := if p 162 then d12 p else d3759 p
theorem agree3856 (p q : Pattern) (h : Agree support p q) : d3856 p = d3856 q := by
  simp only [d3856, h 162 (by decide), agree12 p q h, agree3759 p q h]
theorem nonnegative3856 (p : Pattern) : 0 ≤ d3856 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3759 p)
def d3857 (p : Pattern) : Int := if p 161 then d12 p else d3856 p
theorem agree3857 (p q : Pattern) (h : Agree support p q) : d3857 p = d3857 q := by
  simp only [d3857, h 161 (by decide), agree12 p q h, agree3856 p q h]
theorem nonnegative3857 (p : Pattern) : 0 ≤ d3857 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3856 p)
def d3858 (p : Pattern) : Int := if p 160 then d12 p else d3857 p
theorem agree3858 (p q : Pattern) (h : Agree support p q) : d3858 p = d3858 q := by
  simp only [d3858, h 160 (by decide), agree12 p q h, agree3857 p q h]
theorem nonnegative3858 (p : Pattern) : 0 ≤ d3858 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative3857 p)
def d3859 (p : Pattern) : Int := if p 141 then d12 p else d3858 p
theorem agree3859 (p q : Pattern) (h : Agree support p q) : d3859 p = d3859 q := by
  simp only [d3859, h 141 (by decide), agree12 p q h, agree3858 p q h]
theorem nonnegative3859 (p : Pattern) : 0 ≤ d3859 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative3858 p)
def d3860 (p : Pattern) : Int := if p 138 then d3859 p else d3854 p
theorem agree3860 (p q : Pattern) (h : Agree support p q) : d3860 p = d3860 q := by
  simp only [d3860, h 138 (by decide), agree3859 p q h, agree3854 p q h]
theorem nonnegative3860 (p : Pattern) : 0 ≤ d3860 p :=
  nonnegative_ite (p 138) (nonnegative3859 p) (nonnegative3854 p)
def d3861 (p : Pattern) : Int := if p 116 then d3860 p else d3855 p
theorem agree3861 (p q : Pattern) (h : Agree support p q) : d3861 p = d3861 q := by
  simp only [d3861, h 116 (by decide), agree3860 p q h, agree3855 p q h]
theorem nonnegative3861 (p : Pattern) : 0 ≤ d3861 p :=
  nonnegative_ite (p 116) (nonnegative3860 p) (nonnegative3855 p)
def d3862 (p : Pattern) : Int := if p 162 then d3757 p else d3746 p
theorem agree3862 (p q : Pattern) (h : Agree support p q) : d3862 p = d3862 q := by
  simp only [d3862, h 162 (by decide), agree3757 p q h, agree3746 p q h]
theorem nonnegative3862 (p : Pattern) : 0 ≤ d3862 p :=
  nonnegative_ite (p 162) (nonnegative3757 p) (nonnegative3746 p)
def d3863 (p : Pattern) : Int := if p 161 then d3760 p else d3862 p
theorem agree3863 (p q : Pattern) (h : Agree support p q) : d3863 p = d3863 q := by
  simp only [d3863, h 161 (by decide), agree3760 p q h, agree3862 p q h]
theorem nonnegative3863 (p : Pattern) : 0 ≤ d3863 p :=
  nonnegative_ite (p 161) (nonnegative3760 p) (nonnegative3862 p)
def d3864 (p : Pattern) : Int := if p 160 then d3792 p else d3863 p
theorem agree3864 (p q : Pattern) (h : Agree support p q) : d3864 p = d3864 q := by
  simp only [d3864, h 160 (by decide), agree3792 p q h, agree3863 p q h]
theorem nonnegative3864 (p : Pattern) : 0 ≤ d3864 p :=
  nonnegative_ite (p 160) (nonnegative3792 p) (nonnegative3863 p)
def d3865 (p : Pattern) : Int := if p 141 then d3816 p else d3864 p
theorem agree3865 (p q : Pattern) (h : Agree support p q) : d3865 p = d3865 q := by
  simp only [d3865, h 141 (by decide), agree3816 p q h, agree3864 p q h]
theorem nonnegative3865 (p : Pattern) : 0 ≤ d3865 p :=
  nonnegative_ite (p 141) (nonnegative3816 p) (nonnegative3864 p)
def d3866 (p : Pattern) : Int := if p 138 then d3854 p else d3865 p
theorem agree3866 (p q : Pattern) (h : Agree support p q) : d3866 p = d3866 q := by
  simp only [d3866, h 138 (by decide), agree3854 p q h, agree3865 p q h]
theorem nonnegative3866 (p : Pattern) : 0 ≤ d3866 p :=
  nonnegative_ite (p 138) (nonnegative3854 p) (nonnegative3865 p)
def d3867 (p : Pattern) : Int := if p 138 then d12 p else d3854 p
theorem agree3867 (p q : Pattern) (h : Agree support p q) : d3867 p = d3867 q := by
  simp only [d3867, h 138 (by decide), agree12 p q h, agree3854 p q h]
theorem nonnegative3867 (p : Pattern) : 0 ≤ d3867 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3854 p)
def d3868 (p : Pattern) : Int := if p 116 then d3867 p else d3866 p
theorem agree3868 (p q : Pattern) (h : Agree support p q) : d3868 p = d3868 q := by
  simp only [d3868, h 116 (by decide), agree3867 p q h, agree3866 p q h]
theorem nonnegative3868 (p : Pattern) : 0 ≤ d3868 p :=
  nonnegative_ite (p 116) (nonnegative3867 p) (nonnegative3866 p)
def d3869 (p : Pattern) : Int := if p 115 then d3868 p else d3861 p
theorem agree3869 (p q : Pattern) (h : Agree support p q) : d3869 p = d3869 q := by
  simp only [d3869, h 115 (by decide), agree3868 p q h, agree3861 p q h]
theorem nonnegative3869 (p : Pattern) : 0 ≤ d3869 p :=
  nonnegative_ite (p 115) (nonnegative3868 p) (nonnegative3861 p)
def d3870 (p : Pattern) : Int := if p 71 then d3869 p else d3718 p
theorem agree3870 (p q : Pattern) (h : Agree support p q) : d3870 p = d3870 q := by
  simp only [d3870, h 71 (by decide), agree3869 p q h, agree3718 p q h]
theorem nonnegative3870 (p : Pattern) : 0 ≤ d3870 p :=
  nonnegative_ite (p 71) (nonnegative3869 p) (nonnegative3718 p)
def d3871 (p : Pattern) : Int := if p 49 then d3870 p else d3732 p
theorem agree3871 (p q : Pattern) (h : Agree support p q) : d3871 p = d3871 q := by
  simp only [d3871, h 49 (by decide), agree3870 p q h, agree3732 p q h]
theorem nonnegative3871 (p : Pattern) : 0 ≤ d3871 p :=
  nonnegative_ite (p 49) (nonnegative3870 p) (nonnegative3732 p)
def d3872 (p : Pattern) : Int := if p 225 then d3601 p else d3555 p
theorem agree3872 (p q : Pattern) (h : Agree support p q) : d3872 p = d3872 q := by
  simp only [d3872, h 225 (by decide), agree3601 p q h, agree3555 p q h]
theorem nonnegative3872 (p : Pattern) : 0 ≤ d3872 p :=
  nonnegative_ite (p 225) (nonnegative3601 p) (nonnegative3555 p)
def d3873 (p : Pattern) : Int := if p 224 then d3872 p else d3602 p
theorem agree3873 (p q : Pattern) (h : Agree support p q) : d3873 p = d3873 q := by
  simp only [d3873, h 224 (by decide), agree3872 p q h, agree3602 p q h]
theorem nonnegative3873 (p : Pattern) : 0 ≤ d3873 p :=
  nonnegative_ite (p 224) (nonnegative3872 p) (nonnegative3602 p)
def d3874 (p : Pattern) : Int := if p 204 then d3873 p else d17 p
theorem agree3874 (p q : Pattern) (h : Agree support p q) : d3874 p = d3874 q := by
  simp only [d3874, h 204 (by decide), agree3873 p q h, agree17 p q h]
theorem nonnegative3874 (p : Pattern) : 0 ≤ d3874 p :=
  nonnegative_ite (p 204) (nonnegative3873 p) (nonnegative17 p)
def d3875 (p : Pattern) : Int := if p 204 then d12 p else d3557 p
theorem agree3875 (p q : Pattern) (h : Agree support p q) : d3875 p = d3875 q := by
  simp only [d3875, h 204 (by decide), agree12 p q h, agree3557 p q h]
theorem nonnegative3875 (p : Pattern) : 0 ≤ d3875 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3557 p)
def d3876 (p : Pattern) : Int := if p 182 then d3875 p else d3874 p
theorem agree3876 (p q : Pattern) (h : Agree support p q) : d3876 p = d3876 q := by
  simp only [d3876, h 182 (by decide), agree3875 p q h, agree3874 p q h]
theorem nonnegative3876 (p : Pattern) : 0 ≤ d3876 p :=
  nonnegative_ite (p 182) (nonnegative3875 p) (nonnegative3874 p)
def d3877 (p : Pattern) : Int := if p 163 then d3876 p else d3660 p
theorem agree3877 (p q : Pattern) (h : Agree support p q) : d3877 p = d3877 q := by
  simp only [d3877, h 163 (by decide), agree3876 p q h, agree3660 p q h]
theorem nonnegative3877 (p : Pattern) : 0 ≤ d3877 p :=
  nonnegative_ite (p 163) (nonnegative3876 p) (nonnegative3660 p)
def d3878 (p : Pattern) : Int := if p 162 then d3877 p else d3660 p
theorem agree3878 (p q : Pattern) (h : Agree support p q) : d3878 p = d3878 q := by
  simp only [d3878, h 162 (by decide), agree3877 p q h, agree3660 p q h]
theorem nonnegative3878 (p : Pattern) : 0 ≤ d3878 p :=
  nonnegative_ite (p 162) (nonnegative3877 p) (nonnegative3660 p)
def d3879 (p : Pattern) : Int := if p 162 then d3675 p else d3877 p
theorem agree3879 (p q : Pattern) (h : Agree support p q) : d3879 p = d3879 q := by
  simp only [d3879, h 162 (by decide), agree3675 p q h, agree3877 p q h]
theorem nonnegative3879 (p : Pattern) : 0 ≤ d3879 p :=
  nonnegative_ite (p 162) (nonnegative3675 p) (nonnegative3877 p)
def d3880 (p : Pattern) : Int := if p 161 then d3879 p else d3878 p
theorem agree3880 (p q : Pattern) (h : Agree support p q) : d3880 p = d3880 q := by
  simp only [d3880, h 161 (by decide), agree3879 p q h, agree3878 p q h]
theorem nonnegative3880 (p : Pattern) : 0 ≤ d3880 p :=
  nonnegative_ite (p 161) (nonnegative3879 p) (nonnegative3878 p)
def d3881 (p : Pattern) : Int := if p 182 then d3594 p else d3643 p
theorem agree3881 (p q : Pattern) (h : Agree support p q) : d3881 p = d3881 q := by
  simp only [d3881, h 182 (by decide), agree3594 p q h, agree3643 p q h]
theorem nonnegative3881 (p : Pattern) : 0 ≤ d3881 p :=
  nonnegative_ite (p 182) (nonnegative3594 p) (nonnegative3643 p)
def d3882 (p : Pattern) : Int := if p 163 then d3881 p else d3678 p
theorem agree3882 (p q : Pattern) (h : Agree support p q) : d3882 p = d3882 q := by
  simp only [d3882, h 163 (by decide), agree3881 p q h, agree3678 p q h]
theorem nonnegative3882 (p : Pattern) : 0 ≤ d3882 p :=
  nonnegative_ite (p 163) (nonnegative3881 p) (nonnegative3678 p)
def d3883 (p : Pattern) : Int := if p 182 then d3599 p else d3643 p
theorem agree3883 (p q : Pattern) (h : Agree support p q) : d3883 p = d3883 q := by
  simp only [d3883, h 182 (by decide), agree3599 p q h, agree3643 p q h]
theorem nonnegative3883 (p : Pattern) : 0 ≤ d3883 p :=
  nonnegative_ite (p 182) (nonnegative3599 p) (nonnegative3643 p)
def d3884 (p : Pattern) : Int := if p 182 then d12 p else d3679 p
theorem agree3884 (p q : Pattern) (h : Agree support p q) : d3884 p = d3884 q := by
  simp only [d3884, h 182 (by decide), agree12 p q h, agree3679 p q h]
theorem nonnegative3884 (p : Pattern) : 0 ≤ d3884 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3679 p)
def d3885 (p : Pattern) : Int := if p 163 then d3884 p else d3883 p
theorem agree3885 (p q : Pattern) (h : Agree support p q) : d3885 p = d3885 q := by
  simp only [d3885, h 163 (by decide), agree3884 p q h, agree3883 p q h]
theorem nonnegative3885 (p : Pattern) : 0 ≤ d3885 p :=
  nonnegative_ite (p 163) (nonnegative3884 p) (nonnegative3883 p)
def d3886 (p : Pattern) : Int := if p 162 then d3885 p else d3882 p
theorem agree3886 (p q : Pattern) (h : Agree support p q) : d3886 p = d3886 q := by
  simp only [d3886, h 162 (by decide), agree3885 p q h, agree3882 p q h]
theorem nonnegative3886 (p : Pattern) : 0 ≤ d3886 p :=
  nonnegative_ite (p 162) (nonnegative3885 p) (nonnegative3882 p)
def d3887 (p : Pattern) : Int := if p 163 then d3884 p else d3644 p
theorem agree3887 (p q : Pattern) (h : Agree support p q) : d3887 p = d3887 q := by
  simp only [d3887, h 163 (by decide), agree3884 p q h, agree3644 p q h]
theorem nonnegative3887 (p : Pattern) : 0 ≤ d3887 p :=
  nonnegative_ite (p 163) (nonnegative3884 p) (nonnegative3644 p)
def d3888 (p : Pattern) : Int := if p 162 then d3651 p else d3887 p
theorem agree3888 (p q : Pattern) (h : Agree support p q) : d3888 p = d3888 q := by
  simp only [d3888, h 162 (by decide), agree3651 p q h, agree3887 p q h]
theorem nonnegative3888 (p : Pattern) : 0 ≤ d3888 p :=
  nonnegative_ite (p 162) (nonnegative3651 p) (nonnegative3887 p)
def d3889 (p : Pattern) : Int := if p 161 then d3888 p else d3886 p
theorem agree3889 (p q : Pattern) (h : Agree support p q) : d3889 p = d3889 q := by
  simp only [d3889, h 161 (by decide), agree3888 p q h, agree3886 p q h]
theorem nonnegative3889 (p : Pattern) : 0 ≤ d3889 p :=
  nonnegative_ite (p 161) (nonnegative3888 p) (nonnegative3886 p)
def d3890 (p : Pattern) : Int := if p 160 then d3889 p else d3880 p
theorem agree3890 (p q : Pattern) (h : Agree support p q) : d3890 p = d3890 q := by
  simp only [d3890, h 160 (by decide), agree3889 p q h, agree3880 p q h]
theorem nonnegative3890 (p : Pattern) : 0 ≤ d3890 p :=
  nonnegative_ite (p 160) (nonnegative3889 p) (nonnegative3880 p)
def d3891 (p : Pattern) : Int := if p 225 then d3583 p else d3585 p
theorem agree3891 (p q : Pattern) (h : Agree support p q) : d3891 p = d3891 q := by
  simp only [d3891, h 225 (by decide), agree3583 p q h, agree3585 p q h]
theorem nonnegative3891 (p : Pattern) : 0 ≤ d3891 p :=
  nonnegative_ite (p 225) (nonnegative3583 p) (nonnegative3585 p)
def d3892 (p : Pattern) : Int := if p 224 then d3891 p else d3584 p
theorem agree3892 (p q : Pattern) (h : Agree support p q) : d3892 p = d3892 q := by
  simp only [d3892, h 224 (by decide), agree3891 p q h, agree3584 p q h]
theorem nonnegative3892 (p : Pattern) : 0 ≤ d3892 p :=
  nonnegative_ite (p 224) (nonnegative3891 p) (nonnegative3584 p)
def d3893 (p : Pattern) : Int := if p 204 then d3892 p else d30 p
theorem agree3893 (p q : Pattern) (h : Agree support p q) : d3893 p = d3893 q := by
  simp only [d3893, h 204 (by decide), agree3892 p q h, agree30 p q h]
theorem nonnegative3893 (p : Pattern) : 0 ≤ d3893 p :=
  nonnegative_ite (p 204) (nonnegative3892 p) (nonnegative30 p)
def d3894 (p : Pattern) : Int := if p 204 then d12 p else d3622 p
theorem agree3894 (p q : Pattern) (h : Agree support p q) : d3894 p = d3894 q := by
  simp only [d3894, h 204 (by decide), agree12 p q h, agree3622 p q h]
theorem nonnegative3894 (p : Pattern) : 0 ≤ d3894 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3622 p)
def d3895 (p : Pattern) : Int := if p 182 then d3894 p else d3893 p
theorem agree3895 (p q : Pattern) (h : Agree support p q) : d3895 p = d3895 q := by
  simp only [d3895, h 182 (by decide), agree3894 p q h, agree3893 p q h]
theorem nonnegative3895 (p : Pattern) : 0 ≤ d3895 p :=
  nonnegative_ite (p 182) (nonnegative3894 p) (nonnegative3893 p)
def d3896 (p : Pattern) : Int := if p 163 then d3895 p else d3660 p
theorem agree3896 (p q : Pattern) (h : Agree support p q) : d3896 p = d3896 q := by
  simp only [d3896, h 163 (by decide), agree3895 p q h, agree3660 p q h]
theorem nonnegative3896 (p : Pattern) : 0 ≤ d3896 p :=
  nonnegative_ite (p 163) (nonnegative3895 p) (nonnegative3660 p)
def d3897 (p : Pattern) : Int := if p 163 then d3674 p else d3876 p
theorem agree3897 (p q : Pattern) (h : Agree support p q) : d3897 p = d3897 q := by
  simp only [d3897, h 163 (by decide), agree3674 p q h, agree3876 p q h]
theorem nonnegative3897 (p : Pattern) : 0 ≤ d3897 p :=
  nonnegative_ite (p 163) (nonnegative3674 p) (nonnegative3876 p)
def d3898 (p : Pattern) : Int := if p 162 then d3897 p else d3896 p
theorem agree3898 (p q : Pattern) (h : Agree support p q) : d3898 p = d3898 q := by
  simp only [d3898, h 162 (by decide), agree3897 p q h, agree3896 p q h]
theorem nonnegative3898 (p : Pattern) : 0 ≤ d3898 p :=
  nonnegative_ite (p 162) (nonnegative3897 p) (nonnegative3896 p)
def d3899 (p : Pattern) : Int := if p 163 then d3636 p else d3876 p
theorem agree3899 (p q : Pattern) (h : Agree support p q) : d3899 p = d3899 q := by
  simp only [d3899, h 163 (by decide), agree3636 p q h, agree3876 p q h]
theorem nonnegative3899 (p : Pattern) : 0 ≤ d3899 p :=
  nonnegative_ite (p 163) (nonnegative3636 p) (nonnegative3876 p)
def d3900 (p : Pattern) : Int := if p 162 then d3640 p else d3899 p
theorem agree3900 (p q : Pattern) (h : Agree support p q) : d3900 p = d3900 q := by
  simp only [d3900, h 162 (by decide), agree3640 p q h, agree3899 p q h]
theorem nonnegative3900 (p : Pattern) : 0 ≤ d3900 p :=
  nonnegative_ite (p 162) (nonnegative3640 p) (nonnegative3899 p)
def d3901 (p : Pattern) : Int := if p 161 then d3900 p else d3898 p
theorem agree3901 (p q : Pattern) (h : Agree support p q) : d3901 p = d3901 q := by
  simp only [d3901, h 161 (by decide), agree3900 p q h, agree3898 p q h]
theorem nonnegative3901 (p : Pattern) : 0 ≤ d3901 p :=
  nonnegative_ite (p 161) (nonnegative3900 p) (nonnegative3898 p)
def d3902 (p : Pattern) : Int := if p 163 then d3606 p else d3881 p
theorem agree3902 (p q : Pattern) (h : Agree support p q) : d3902 p = d3902 q := by
  simp only [d3902, h 163 (by decide), agree3606 p q h, agree3881 p q h]
theorem nonnegative3902 (p : Pattern) : 0 ≤ d3902 p :=
  nonnegative_ite (p 163) (nonnegative3606 p) (nonnegative3881 p)
def d3903 (p : Pattern) : Int := if p 163 then d3650 p else d3884 p
theorem agree3903 (p q : Pattern) (h : Agree support p q) : d3903 p = d3903 q := by
  simp only [d3903, h 163 (by decide), agree3650 p q h, agree3884 p q h]
theorem nonnegative3903 (p : Pattern) : 0 ≤ d3903 p :=
  nonnegative_ite (p 163) (nonnegative3650 p) (nonnegative3884 p)
def d3904 (p : Pattern) : Int := if p 162 then d3903 p else d3902 p
theorem agree3904 (p q : Pattern) (h : Agree support p q) : d3904 p = d3904 q := by
  simp only [d3904, h 162 (by decide), agree3903 p q h, agree3902 p q h]
theorem nonnegative3904 (p : Pattern) : 0 ≤ d3904 p :=
  nonnegative_ite (p 162) (nonnegative3903 p) (nonnegative3902 p)
def d3905 (p : Pattern) : Int := if p 163 then d12 p else d3884 p
theorem agree3905 (p q : Pattern) (h : Agree support p q) : d3905 p = d3905 q := by
  simp only [d3905, h 163 (by decide), agree12 p q h, agree3884 p q h]
theorem nonnegative3905 (p : Pattern) : 0 ≤ d3905 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3884 p)
def d3906 (p : Pattern) : Int := if p 162 then d12 p else d3905 p
theorem agree3906 (p q : Pattern) (h : Agree support p q) : d3906 p = d3906 q := by
  simp only [d3906, h 162 (by decide), agree12 p q h, agree3905 p q h]
theorem nonnegative3906 (p : Pattern) : 0 ≤ d3906 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3905 p)
def d3907 (p : Pattern) : Int := if p 161 then d3906 p else d3904 p
theorem agree3907 (p q : Pattern) (h : Agree support p q) : d3907 p = d3907 q := by
  simp only [d3907, h 161 (by decide), agree3906 p q h, agree3904 p q h]
theorem nonnegative3907 (p : Pattern) : 0 ≤ d3907 p :=
  nonnegative_ite (p 161) (nonnegative3906 p) (nonnegative3904 p)
def d3908 (p : Pattern) : Int := if p 160 then d3907 p else d3901 p
theorem agree3908 (p q : Pattern) (h : Agree support p q) : d3908 p = d3908 q := by
  simp only [d3908, h 160 (by decide), agree3907 p q h, agree3901 p q h]
theorem nonnegative3908 (p : Pattern) : 0 ≤ d3908 p :=
  nonnegative_ite (p 160) (nonnegative3907 p) (nonnegative3901 p)
def d3909 (p : Pattern) : Int := if p 141 then d3908 p else d3890 p
theorem agree3909 (p q : Pattern) (h : Agree support p q) : d3909 p = d3909 q := by
  simp only [d3909, h 141 (by decide), agree3908 p q h, agree3890 p q h]
theorem nonnegative3909 (p : Pattern) : 0 ≤ d3909 p :=
  nonnegative_ite (p 141) (nonnegative3908 p) (nonnegative3890 p)
def d3910 (p : Pattern) : Int := if p 204 then d3663 p else d13 p
theorem agree3910 (p q : Pattern) (h : Agree support p q) : d3910 p = d3910 q := by
  simp only [d3910, h 204 (by decide), agree3663 p q h, agree13 p q h]
theorem nonnegative3910 (p : Pattern) : 0 ≤ d3910 p :=
  nonnegative_ite (p 204) (nonnegative3663 p) (nonnegative13 p)
def d3911 (p : Pattern) : Int := if p 204 then d12 p else d3657 p
theorem agree3911 (p q : Pattern) (h : Agree support p q) : d3911 p = d3911 q := by
  simp only [d3911, h 204 (by decide), agree12 p q h, agree3657 p q h]
theorem nonnegative3911 (p : Pattern) : 0 ≤ d3911 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3657 p)
def d3912 (p : Pattern) : Int := if p 182 then d3911 p else d3910 p
theorem agree3912 (p q : Pattern) (h : Agree support p q) : d3912 p = d3912 q := by
  simp only [d3912, h 182 (by decide), agree3911 p q h, agree3910 p q h]
theorem nonnegative3912 (p : Pattern) : 0 ≤ d3912 p :=
  nonnegative_ite (p 182) (nonnegative3911 p) (nonnegative3910 p)
def d3913 (p : Pattern) : Int := if p 163 then d3668 p else d3912 p
theorem agree3913 (p q : Pattern) (h : Agree support p q) : d3913 p = d3913 q := by
  simp only [d3913, h 163 (by decide), agree3668 p q h, agree3912 p q h]
theorem nonnegative3913 (p : Pattern) : 0 ≤ d3913 p :=
  nonnegative_ite (p 163) (nonnegative3668 p) (nonnegative3912 p)
def d3914 (p : Pattern) : Int := if p 162 then d3681 p else d3913 p
theorem agree3914 (p q : Pattern) (h : Agree support p q) : d3914 p = d3914 q := by
  simp only [d3914, h 162 (by decide), agree3681 p q h, agree3913 p q h]
theorem nonnegative3914 (p : Pattern) : 0 ≤ d3914 p :=
  nonnegative_ite (p 162) (nonnegative3681 p) (nonnegative3913 p)
def d3915 (p : Pattern) : Int := if p 161 then d3682 p else d3914 p
theorem agree3915 (p q : Pattern) (h : Agree support p q) : d3915 p = d3915 q := by
  simp only [d3915, h 161 (by decide), agree3682 p q h, agree3914 p q h]
theorem nonnegative3915 (p : Pattern) : 0 ≤ d3915 p :=
  nonnegative_ite (p 161) (nonnegative3682 p) (nonnegative3914 p)
def d3916 (p : Pattern) : Int := if p 225 then d315 p else d190 p
theorem agree3916 (p q : Pattern) (h : Agree support p q) : d3916 p = d3916 q := by
  simp only [d3916, h 225 (by decide), agree315 p q h, agree190 p q h]
theorem nonnegative3916 (p : Pattern) : 0 ≤ d3916 p :=
  nonnegative_ite (p 225) (nonnegative315 p) (nonnegative190 p)
def d3917 (p : Pattern) : Int := if p 224 then d315 p else d3916 p
theorem agree3917 (p q : Pattern) (h : Agree support p q) : d3917 p = d3917 q := by
  simp only [d3917, h 224 (by decide), agree315 p q h, agree3916 p q h]
theorem nonnegative3917 (p : Pattern) : 0 ≤ d3917 p :=
  nonnegative_ite (p 224) (nonnegative315 p) (nonnegative3916 p)
def d3918 (p : Pattern) : Int := if p 204 then d3917 p else d190 p
theorem agree3918 (p q : Pattern) (h : Agree support p q) : d3918 p = d3918 q := by
  simp only [d3918, h 204 (by decide), agree3917 p q h, agree190 p q h]
theorem nonnegative3918 (p : Pattern) : 0 ≤ d3918 p :=
  nonnegative_ite (p 204) (nonnegative3917 p) (nonnegative190 p)
def d3919 (p : Pattern) : Int := if p 204 then d12 p else d3917 p
theorem agree3919 (p q : Pattern) (h : Agree support p q) : d3919 p = d3919 q := by
  simp only [d3919, h 204 (by decide), agree12 p q h, agree3917 p q h]
theorem nonnegative3919 (p : Pattern) : 0 ≤ d3919 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3917 p)
def d3920 (p : Pattern) : Int := if p 182 then d3919 p else d3918 p
theorem agree3920 (p q : Pattern) (h : Agree support p q) : d3920 p = d3920 q := by
  simp only [d3920, h 182 (by decide), agree3919 p q h, agree3918 p q h]
theorem nonnegative3920 (p : Pattern) : 0 ≤ d3920 p :=
  nonnegative_ite (p 182) (nonnegative3919 p) (nonnegative3918 p)
def d3921 (p : Pattern) : Int := if p 163 then d3920 p else d3670 p
theorem agree3921 (p q : Pattern) (h : Agree support p q) : d3921 p = d3921 q := by
  simp only [d3921, h 163 (by decide), agree3920 p q h, agree3670 p q h]
theorem nonnegative3921 (p : Pattern) : 0 ≤ d3921 p :=
  nonnegative_ite (p 163) (nonnegative3920 p) (nonnegative3670 p)
def d3922 (p : Pattern) : Int := if p 162 then d12 p else d3921 p
theorem agree3922 (p q : Pattern) (h : Agree support p q) : d3922 p = d3922 q := by
  simp only [d3922, h 162 (by decide), agree12 p q h, agree3921 p q h]
theorem nonnegative3922 (p : Pattern) : 0 ≤ d3922 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3921 p)
def d3923 (p : Pattern) : Int := if p 161 then d12 p else d3922 p
theorem agree3923 (p q : Pattern) (h : Agree support p q) : d3923 p = d3923 q := by
  simp only [d3923, h 161 (by decide), agree12 p q h, agree3922 p q h]
theorem nonnegative3923 (p : Pattern) : 0 ≤ d3923 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3922 p)
def d3924 (p : Pattern) : Int := if p 160 then d3923 p else d3915 p
theorem agree3924 (p q : Pattern) (h : Agree support p q) : d3924 p = d3924 q := by
  simp only [d3924, h 160 (by decide), agree3923 p q h, agree3915 p q h]
theorem nonnegative3924 (p : Pattern) : 0 ≤ d3924 p :=
  nonnegative_ite (p 160) (nonnegative3923 p) (nonnegative3915 p)
def d3925 (p : Pattern) : Int := if p 246 then d57 p else d30 p
theorem agree3925 (p q : Pattern) (h : Agree support p q) : d3925 p = d3925 q := by
  simp only [d3925, h 246 (by decide), agree57 p q h, agree30 p q h]
theorem nonnegative3925 (p : Pattern) : 0 ≤ d3925 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative30 p)
def d3926 (p : Pattern) : Int := if p 225 then d3925 p else d3585 p
theorem agree3926 (p q : Pattern) (h : Agree support p q) : d3926 p = d3926 q := by
  simp only [d3926, h 225 (by decide), agree3925 p q h, agree3585 p q h]
theorem nonnegative3926 (p : Pattern) : 0 ≤ d3926 p :=
  nonnegative_ite (p 225) (nonnegative3925 p) (nonnegative3585 p)
def d3927 (p : Pattern) : Int := if p 224 then d3926 p else d3584 p
theorem agree3927 (p q : Pattern) (h : Agree support p q) : d3927 p = d3927 q := by
  simp only [d3927, h 224 (by decide), agree3926 p q h, agree3584 p q h]
theorem nonnegative3927 (p : Pattern) : 0 ≤ d3927 p :=
  nonnegative_ite (p 224) (nonnegative3926 p) (nonnegative3584 p)
def d3928 (p : Pattern) : Int := if p 204 then d12 p else d3927 p
theorem agree3928 (p q : Pattern) (h : Agree support p q) : d3928 p = d3928 q := by
  simp only [d3928, h 204 (by decide), agree12 p q h, agree3927 p q h]
theorem nonnegative3928 (p : Pattern) : 0 ≤ d3928 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3927 p)
def d3929 (p : Pattern) : Int := if p 182 then d3928 p else d3643 p
theorem agree3929 (p q : Pattern) (h : Agree support p q) : d3929 p = d3929 q := by
  simp only [d3929, h 182 (by decide), agree3928 p q h, agree3643 p q h]
theorem nonnegative3929 (p : Pattern) : 0 ≤ d3929 p :=
  nonnegative_ite (p 182) (nonnegative3928 p) (nonnegative3643 p)
def d3930 (p : Pattern) : Int := if p 163 then d3678 p else d3929 p
theorem agree3930 (p q : Pattern) (h : Agree support p q) : d3930 p = d3930 q := by
  simp only [d3930, h 163 (by decide), agree3678 p q h, agree3929 p q h]
theorem nonnegative3930 (p : Pattern) : 0 ≤ d3930 p :=
  nonnegative_ite (p 163) (nonnegative3678 p) (nonnegative3929 p)
def d3931 (p : Pattern) : Int := if p 163 then d3639 p else d3670 p
theorem agree3931 (p q : Pattern) (h : Agree support p q) : d3931 p = d3931 q := by
  simp only [d3931, h 163 (by decide), agree3639 p q h, agree3670 p q h]
theorem nonnegative3931 (p : Pattern) : 0 ≤ d3931 p :=
  nonnegative_ite (p 163) (nonnegative3639 p) (nonnegative3670 p)
def d3932 (p : Pattern) : Int := if p 162 then d3931 p else d3930 p
theorem agree3932 (p q : Pattern) (h : Agree support p q) : d3932 p = d3932 q := by
  simp only [d3932, h 162 (by decide), agree3931 p q h, agree3930 p q h]
theorem nonnegative3932 (p : Pattern) : 0 ≤ d3932 p :=
  nonnegative_ite (p 162) (nonnegative3931 p) (nonnegative3930 p)
def d3933 (p : Pattern) : Int := if p 161 then d3692 p else d3932 p
theorem agree3933 (p q : Pattern) (h : Agree support p q) : d3933 p = d3933 q := by
  simp only [d3933, h 161 (by decide), agree3692 p q h, agree3932 p q h]
theorem nonnegative3933 (p : Pattern) : 0 ≤ d3933 p :=
  nonnegative_ite (p 161) (nonnegative3692 p) (nonnegative3932 p)
def d3934 (p : Pattern) : Int := if p 163 then d12 p else d3920 p
theorem agree3934 (p q : Pattern) (h : Agree support p q) : d3934 p = d3934 q := by
  simp only [d3934, h 163 (by decide), agree12 p q h, agree3920 p q h]
theorem nonnegative3934 (p : Pattern) : 0 ≤ d3934 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3920 p)
def d3935 (p : Pattern) : Int := if p 162 then d12 p else d3934 p
theorem agree3935 (p q : Pattern) (h : Agree support p q) : d3935 p = d3935 q := by
  simp only [d3935, h 162 (by decide), agree12 p q h, agree3934 p q h]
theorem nonnegative3935 (p : Pattern) : 0 ≤ d3935 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3934 p)
def d3936 (p : Pattern) : Int := if p 161 then d12 p else d3935 p
theorem agree3936 (p q : Pattern) (h : Agree support p q) : d3936 p = d3936 q := by
  simp only [d3936, h 161 (by decide), agree12 p q h, agree3935 p q h]
theorem nonnegative3936 (p : Pattern) : 0 ≤ d3936 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3935 p)
def d3937 (p : Pattern) : Int := if p 160 then d3936 p else d3933 p
theorem agree3937 (p q : Pattern) (h : Agree support p q) : d3937 p = d3937 q := by
  simp only [d3937, h 160 (by decide), agree3936 p q h, agree3933 p q h]
theorem nonnegative3937 (p : Pattern) : 0 ≤ d3937 p :=
  nonnegative_ite (p 160) (nonnegative3936 p) (nonnegative3933 p)
def d3938 (p : Pattern) : Int := if p 141 then d3937 p else d3924 p
theorem agree3938 (p q : Pattern) (h : Agree support p q) : d3938 p = d3938 q := by
  simp only [d3938, h 141 (by decide), agree3937 p q h, agree3924 p q h]
theorem nonnegative3938 (p : Pattern) : 0 ≤ d3938 p :=
  nonnegative_ite (p 141) (nonnegative3937 p) (nonnegative3924 p)
def d3939 (p : Pattern) : Int := if p 138 then d3938 p else d3909 p
theorem agree3939 (p q : Pattern) (h : Agree support p q) : d3939 p = d3939 q := by
  simp only [d3939, h 138 (by decide), agree3938 p q h, agree3909 p q h]
theorem nonnegative3939 (p : Pattern) : 0 ≤ d3939 p :=
  nonnegative_ite (p 138) (nonnegative3938 p) (nonnegative3909 p)
def d3940 (p : Pattern) : Int := if p 138 then d12 p else d3938 p
theorem agree3940 (p q : Pattern) (h : Agree support p q) : d3940 p = d3940 q := by
  simp only [d3940, h 138 (by decide), agree12 p q h, agree3938 p q h]
theorem nonnegative3940 (p : Pattern) : 0 ≤ d3940 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3938 p)
def d3941 (p : Pattern) : Int := if p 116 then d3940 p else d3939 p
theorem agree3941 (p q : Pattern) (h : Agree support p q) : d3941 p = d3941 q := by
  simp only [d3941, h 116 (by decide), agree3940 p q h, agree3939 p q h]
theorem nonnegative3941 (p : Pattern) : 0 ≤ d3941 p :=
  nonnegative_ite (p 116) (nonnegative3940 p) (nonnegative3939 p)
def d3942 (p : Pattern) : Int := if p 115 then d3941 p else d3730 p
theorem agree3942 (p q : Pattern) (h : Agree support p q) : d3942 p = d3942 q := by
  simp only [d3942, h 115 (by decide), agree3941 p q h, agree3730 p q h]
theorem nonnegative3942 (p : Pattern) : 0 ≤ d3942 p :=
  nonnegative_ite (p 115) (nonnegative3941 p) (nonnegative3730 p)
def d3943 (p : Pattern) : Int := if p 71 then d3942 p else d3718 p
theorem agree3943 (p q : Pattern) (h : Agree support p q) : d3943 p = d3943 q := by
  simp only [d3943, h 71 (by decide), agree3942 p q h, agree3718 p q h]
theorem nonnegative3943 (p : Pattern) : 0 ≤ d3943 p :=
  nonnegative_ite (p 71) (nonnegative3942 p) (nonnegative3718 p)
def d3944 (p : Pattern) : Int := if p 163 then d12 p else d3756 p
theorem agree3944 (p q : Pattern) (h : Agree support p q) : d3944 p = d3944 q := by
  simp only [d3944, h 163 (by decide), agree12 p q h, agree3756 p q h]
theorem nonnegative3944 (p : Pattern) : 0 ≤ d3944 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3756 p)
def d3945 (p : Pattern) : Int := if p 162 then d3944 p else d3802 p
theorem agree3945 (p q : Pattern) (h : Agree support p q) : d3945 p = d3945 q := by
  simp only [d3945, h 162 (by decide), agree3944 p q h, agree3802 p q h]
theorem nonnegative3945 (p : Pattern) : 0 ≤ d3945 p :=
  nonnegative_ite (p 162) (nonnegative3944 p) (nonnegative3802 p)
def d3946 (p : Pattern) : Int := if p 162 then d12 p else d3944 p
theorem agree3946 (p q : Pattern) (h : Agree support p q) : d3946 p = d3946 q := by
  simp only [d3946, h 162 (by decide), agree12 p q h, agree3944 p q h]
theorem nonnegative3946 (p : Pattern) : 0 ≤ d3946 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3944 p)
def d3947 (p : Pattern) : Int := if p 161 then d3946 p else d3945 p
theorem agree3947 (p q : Pattern) (h : Agree support p q) : d3947 p = d3947 q := by
  simp only [d3947, h 161 (by decide), agree3946 p q h, agree3945 p q h]
theorem nonnegative3947 (p : Pattern) : 0 ≤ d3947 p :=
  nonnegative_ite (p 161) (nonnegative3946 p) (nonnegative3945 p)
def d3948 (p : Pattern) : Int := if p 163 then d12 p else d3787 p
theorem agree3948 (p q : Pattern) (h : Agree support p q) : d3948 p = d3948 q := by
  simp only [d3948, h 163 (by decide), agree12 p q h, agree3787 p q h]
theorem nonnegative3948 (p : Pattern) : 0 ≤ d3948 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3787 p)
def d3949 (p : Pattern) : Int := if p 162 then d3948 p else d3810 p
theorem agree3949 (p q : Pattern) (h : Agree support p q) : d3949 p = d3949 q := by
  simp only [d3949, h 162 (by decide), agree3948 p q h, agree3810 p q h]
theorem nonnegative3949 (p : Pattern) : 0 ≤ d3949 p :=
  nonnegative_ite (p 162) (nonnegative3948 p) (nonnegative3810 p)
def d3950 (p : Pattern) : Int := if p 162 then d12 p else d3948 p
theorem agree3950 (p q : Pattern) (h : Agree support p q) : d3950 p = d3950 q := by
  simp only [d3950, h 162 (by decide), agree12 p q h, agree3948 p q h]
theorem nonnegative3950 (p : Pattern) : 0 ≤ d3950 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3948 p)
def d3951 (p : Pattern) : Int := if p 161 then d3950 p else d3949 p
theorem agree3951 (p q : Pattern) (h : Agree support p q) : d3951 p = d3951 q := by
  simp only [d3951, h 161 (by decide), agree3950 p q h, agree3949 p q h]
theorem nonnegative3951 (p : Pattern) : 0 ≤ d3951 p :=
  nonnegative_ite (p 161) (nonnegative3950 p) (nonnegative3949 p)
def d3952 (p : Pattern) : Int := if p 160 then d3951 p else d3947 p
theorem agree3952 (p q : Pattern) (h : Agree support p q) : d3952 p = d3952 q := by
  simp only [d3952, h 160 (by decide), agree3951 p q h, agree3947 p q h]
theorem nonnegative3952 (p : Pattern) : 0 ≤ d3952 p :=
  nonnegative_ite (p 160) (nonnegative3951 p) (nonnegative3947 p)
def d3953 (p : Pattern) : Int := if p 141 then d3952 p else d3793 p
theorem agree3953 (p q : Pattern) (h : Agree support p q) : d3953 p = d3953 q := by
  simp only [d3953, h 141 (by decide), agree3952 p q h, agree3793 p q h]
theorem nonnegative3953 (p : Pattern) : 0 ≤ d3953 p :=
  nonnegative_ite (p 141) (nonnegative3952 p) (nonnegative3793 p)
def d3954 (p : Pattern) : Int := if p 163 then d12 p else d3832 p
theorem agree3954 (p q : Pattern) (h : Agree support p q) : d3954 p = d3954 q := by
  simp only [d3954, h 163 (by decide), agree12 p q h, agree3832 p q h]
theorem nonnegative3954 (p : Pattern) : 0 ≤ d3954 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3832 p)
def d3955 (p : Pattern) : Int := if p 162 then d3954 p else d3844 p
theorem agree3955 (p q : Pattern) (h : Agree support p q) : d3955 p = d3955 q := by
  simp only [d3955, h 162 (by decide), agree3954 p q h, agree3844 p q h]
theorem nonnegative3955 (p : Pattern) : 0 ≤ d3955 p :=
  nonnegative_ite (p 162) (nonnegative3954 p) (nonnegative3844 p)
def d3956 (p : Pattern) : Int := if p 162 then d12 p else d3954 p
theorem agree3956 (p q : Pattern) (h : Agree support p q) : d3956 p = d3956 q := by
  simp only [d3956, h 162 (by decide), agree12 p q h, agree3954 p q h]
theorem nonnegative3956 (p : Pattern) : 0 ≤ d3956 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3954 p)
def d3957 (p : Pattern) : Int := if p 161 then d3956 p else d3955 p
theorem agree3957 (p q : Pattern) (h : Agree support p q) : d3957 p = d3957 q := by
  simp only [d3957, h 161 (by decide), agree3956 p q h, agree3955 p q h]
theorem nonnegative3957 (p : Pattern) : 0 ≤ d3957 p :=
  nonnegative_ite (p 161) (nonnegative3956 p) (nonnegative3955 p)
def d3958 (p : Pattern) : Int := if p 160 then d3852 p else d3957 p
theorem agree3958 (p q : Pattern) (h : Agree support p q) : d3958 p = d3958 q := by
  simp only [d3958, h 160 (by decide), agree3852 p q h, agree3957 p q h]
theorem nonnegative3958 (p : Pattern) : 0 ≤ d3958 p :=
  nonnegative_ite (p 160) (nonnegative3852 p) (nonnegative3957 p)
def d3959 (p : Pattern) : Int := if p 141 then d3958 p else d3843 p
theorem agree3959 (p q : Pattern) (h : Agree support p q) : d3959 p = d3959 q := by
  simp only [d3959, h 141 (by decide), agree3958 p q h, agree3843 p q h]
theorem nonnegative3959 (p : Pattern) : 0 ≤ d3959 p :=
  nonnegative_ite (p 141) (nonnegative3958 p) (nonnegative3843 p)
end NetHack.Sokoban22Refined85
