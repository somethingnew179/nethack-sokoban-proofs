/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Nodes06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d840 (p : Pattern) : Int := if p 133 then d839 p else d838 p
theorem agree840 (p q : Pattern) (h : Agree support p q) : d840 p = d840 q := by
  simp only [d840, h 133 (by decide), agree839 p q h, agree838 p q h]
theorem nonnegative840 (p : Pattern) : 0 ≤ d840 p :=
  nonnegative_ite (p 133) (nonnegative839 p) (nonnegative838 p)
def d841 (p : Pattern) : Int := if p 133 then d66 p else d839 p
theorem agree841 (p q : Pattern) (h : Agree support p q) : d841 p = d841 q := by
  simp only [d841, h 133 (by decide), agree66 p q h, agree839 p q h]
theorem nonnegative841 (p : Pattern) : 0 ≤ d841 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative839 p)
def d842 (p : Pattern) : Int := if p 132 then d841 p else d840 p
theorem agree842 (p q : Pattern) (h : Agree support p q) : d842 p = d842 q := by
  simp only [d842, h 132 (by decide), agree841 p q h, agree840 p q h]
theorem nonnegative842 (p : Pattern) : 0 ≤ d842 p :=
  nonnegative_ite (p 132) (nonnegative841 p) (nonnegative840 p)
def d843 (p : Pattern) : Int := if p 108 then d842 p else d837 p
theorem agree843 (p q : Pattern) (h : Agree support p q) : d843 p = d843 q := by
  simp only [d843, h 108 (by decide), agree842 p q h, agree837 p q h]
theorem nonnegative843 (p : Pattern) : 0 ≤ d843 p :=
  nonnegative_ite (p 108) (nonnegative842 p) (nonnegative837 p)
def d844 (p : Pattern) : Int := if p 108 then d71 p else d214 p
theorem agree844 (p q : Pattern) (h : Agree support p q) : d844 p = d844 q := by
  simp only [d844, h 108 (by decide), agree71 p q h, agree214 p q h]
theorem nonnegative844 (p : Pattern) : 0 ≤ d844 p :=
  nonnegative_ite (p 108) (nonnegative71 p) (nonnegative214 p)
def d845 (p : Pattern) : Int := if p 134 then d0 p else d794 p
theorem agree845 (p q : Pattern) (h : Agree support p q) : d845 p = d845 q := by
  simp only [d845, h 134 (by decide), agree0 p q h, agree794 p q h]
theorem nonnegative845 (p : Pattern) : 0 ≤ d845 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative794 p)
def d846 (p : Pattern) : Int := if p 133 then d757 p else d0 p
theorem agree846 (p q : Pattern) (h : Agree support p q) : d846 p = d846 q := by
  simp only [d846, h 133 (by decide), agree757 p q h, agree0 p q h]
theorem nonnegative846 (p : Pattern) : 0 ≤ d846 p :=
  nonnegative_ite (p 133) (nonnegative757 p) (nonnegative0 p)
def d847 (p : Pattern) : Int := if p 133 then d758 p else d1 p
theorem agree847 (p q : Pattern) (h : Agree support p q) : d847 p = d847 q := by
  simp only [d847, h 133 (by decide), agree758 p q h, agree1 p q h]
theorem nonnegative847 (p : Pattern) : 0 ≤ d847 p :=
  nonnegative_ite (p 133) (nonnegative758 p) (nonnegative1 p)
def d848 (p : Pattern) : Int := if p 134 then d0 p else d818 p
theorem agree848 (p q : Pattern) (h : Agree support p q) : d848 p = d848 q := by
  simp only [d848, h 134 (by decide), agree0 p q h, agree818 p q h]
theorem nonnegative848 (p : Pattern) : 0 ≤ d848 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative818 p)
def d849 (p : Pattern) : Int := if p 133 then d848 p else d845 p
theorem agree849 (p q : Pattern) (h : Agree support p q) : d849 p = d849 q := by
  simp only [d849, h 133 (by decide), agree848 p q h, agree845 p q h]
theorem nonnegative849 (p : Pattern) : 0 ≤ d849 p :=
  nonnegative_ite (p 133) (nonnegative848 p) (nonnegative845 p)
def d850 (p : Pattern) : Int := if p 187 then d1 p else d0 p
theorem agree850 (p q : Pattern) (h : Agree support p q) : d850 p = d850 q := by
  simp only [d850, h 187 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative850 (p : Pattern) : 0 ≤ d850 p :=
  nonnegative_ite (p 187) (nonnegative1 p) (nonnegative0 p)
def d851 (p : Pattern) : Int := if p 187 then d0 p else d1 p
theorem agree851 (p q : Pattern) (h : Agree support p q) : d851 p = d851 q := by
  simp only [d851, h 187 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative851 (p : Pattern) : 0 ≤ d851 p :=
  nonnegative_ite (p 187) (nonnegative0 p) (nonnegative1 p)
def d852 (p : Pattern) : Int := if p 132 then d66 p else d70 p
theorem agree852 (p q : Pattern) (h : Agree support p q) : d852 p = d852 q := by
  simp only [d852, h 132 (by decide), agree66 p q h, agree70 p q h]
theorem nonnegative852 (p : Pattern) : 0 ≤ d852 p :=
  nonnegative_ite (p 132) (nonnegative66 p) (nonnegative70 p)
def d853 (p : Pattern) : Int := if p 192 then d1 p else d0 p
theorem agree853 (p q : Pattern) (h : Agree support p q) : d853 p = d853 q := by
  simp only [d853, h 192 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative853 (p : Pattern) : 0 ≤ d853 p :=
  nonnegative_ite (p 192) (nonnegative1 p) (nonnegative0 p)
def d854 (p : Pattern) : Int := if p 192 then d0 p else d1 p
theorem agree854 (p q : Pattern) (h : Agree support p q) : d854 p = d854 q := by
  simp only [d854, h 192 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative854 (p : Pattern) : 0 ≤ d854 p :=
  nonnegative_ite (p 192) (nonnegative0 p) (nonnegative1 p)
def d855 (p : Pattern) : Int := if p 186 then d54 p else d6 p
theorem agree855 (p q : Pattern) (h : Agree support p q) : d855 p = d855 q := by
  simp only [d855, h 186 (by decide), agree54 p q h, agree6 p q h]
theorem nonnegative855 (p : Pattern) : 0 ≤ d855 p :=
  nonnegative_ite (p 186) (nonnegative54 p) (nonnegative6 p)
def d856 (p : Pattern) : Int := if p 160 then d855 p else d6 p
theorem agree856 (p q : Pattern) (h : Agree support p q) : d856 p = d856 q := by
  simp only [d856, h 160 (by decide), agree855 p q h, agree6 p q h]
theorem nonnegative856 (p : Pattern) : 0 ≤ d856 p :=
  nonnegative_ite (p 160) (nonnegative855 p) (nonnegative6 p)
def d857 (p : Pattern) : Int := if p 168 then d10 p else d6 p
theorem agree857 (p q : Pattern) (h : Agree support p q) : d857 p = d857 q := by
  simp only [d857, h 168 (by decide), agree10 p q h, agree6 p q h]
theorem nonnegative857 (p : Pattern) : 0 ≤ d857 p :=
  nonnegative_ite (p 168) (nonnegative10 p) (nonnegative6 p)
def d858 (p : Pattern) : Int := if p 186 then d59 p else d10 p
theorem agree858 (p q : Pattern) (h : Agree support p q) : d858 p = d858 q := by
  simp only [d858, h 186 (by decide), agree59 p q h, agree10 p q h]
theorem nonnegative858 (p : Pattern) : 0 ≤ d858 p :=
  nonnegative_ite (p 186) (nonnegative59 p) (nonnegative10 p)
def d859 (p : Pattern) : Int := if p 168 then d858 p else d855 p
theorem agree859 (p q : Pattern) (h : Agree support p q) : d859 p = d859 q := by
  simp only [d859, h 168 (by decide), agree858 p q h, agree855 p q h]
theorem nonnegative859 (p : Pattern) : 0 ≤ d859 p :=
  nonnegative_ite (p 168) (nonnegative858 p) (nonnegative855 p)
def d860 (p : Pattern) : Int := if p 160 then d859 p else d857 p
theorem agree860 (p q : Pattern) (h : Agree support p q) : d860 p = d860 q := by
  simp only [d860, h 160 (by decide), agree859 p q h, agree857 p q h]
theorem nonnegative860 (p : Pattern) : 0 ≤ d860 p :=
  nonnegative_ite (p 160) (nonnegative859 p) (nonnegative857 p)
def d861 (p : Pattern) : Int := if p 141 then d860 p else d856 p
theorem agree861 (p q : Pattern) (h : Agree support p q) : d861 p = d861 q := by
  simp only [d861, h 141 (by decide), agree860 p q h, agree856 p q h]
theorem nonnegative861 (p : Pattern) : 0 ≤ d861 p :=
  nonnegative_ite (p 141) (nonnegative860 p) (nonnegative856 p)
def d862 (p : Pattern) : Int := if p 160 then d54 p else d6 p
theorem agree862 (p q : Pattern) (h : Agree support p q) : d862 p = d862 q := by
  simp only [d862, h 160 (by decide), agree54 p q h, agree6 p q h]
theorem nonnegative862 (p : Pattern) : 0 ≤ d862 p :=
  nonnegative_ite (p 160) (nonnegative54 p) (nonnegative6 p)
def d863 (p : Pattern) : Int := if p 187 then d54 p else d6 p
theorem agree863 (p q : Pattern) (h : Agree support p q) : d863 p = d863 q := by
  simp only [d863, h 187 (by decide), agree54 p q h, agree6 p q h]
theorem nonnegative863 (p : Pattern) : 0 ≤ d863 p :=
  nonnegative_ite (p 187) (nonnegative54 p) (nonnegative6 p)
def d864 (p : Pattern) : Int := if p 186 then d863 p else d6 p
theorem agree864 (p q : Pattern) (h : Agree support p q) : d864 p = d864 q := by
  simp only [d864, h 186 (by decide), agree863 p q h, agree6 p q h]
theorem nonnegative864 (p : Pattern) : 0 ≤ d864 p :=
  nonnegative_ite (p 186) (nonnegative863 p) (nonnegative6 p)
def d865 (p : Pattern) : Int := if p 160 then d54 p else d864 p
theorem agree865 (p q : Pattern) (h : Agree support p q) : d865 p = d865 q := by
  simp only [d865, h 160 (by decide), agree54 p q h, agree864 p q h]
theorem nonnegative865 (p : Pattern) : 0 ≤ d865 p :=
  nonnegative_ite (p 160) (nonnegative54 p) (nonnegative864 p)
def d866 (p : Pattern) : Int := if p 159 then d865 p else d862 p
theorem agree866 (p q : Pattern) (h : Agree support p q) : d866 p = d866 q := by
  simp only [d866, h 159 (by decide), agree865 p q h, agree862 p q h]
theorem nonnegative866 (p : Pattern) : 0 ≤ d866 p :=
  nonnegative_ite (p 159) (nonnegative865 p) (nonnegative862 p)
def d867 (p : Pattern) : Int := if p 158 then d866 p else d862 p
theorem agree867 (p q : Pattern) (h : Agree support p q) : d867 p = d867 q := by
  simp only [d867, h 158 (by decide), agree866 p q h, agree862 p q h]
theorem nonnegative867 (p : Pattern) : 0 ≤ d867 p :=
  nonnegative_ite (p 158) (nonnegative866 p) (nonnegative862 p)
def d868 (p : Pattern) : Int := if p 168 then d59 p else d54 p
theorem agree868 (p q : Pattern) (h : Agree support p q) : d868 p = d868 q := by
  simp only [d868, h 168 (by decide), agree59 p q h, agree54 p q h]
theorem nonnegative868 (p : Pattern) : 0 ≤ d868 p :=
  nonnegative_ite (p 168) (nonnegative59 p) (nonnegative54 p)
def d869 (p : Pattern) : Int := if p 160 then d868 p else d857 p
theorem agree869 (p q : Pattern) (h : Agree support p q) : d869 p = d869 q := by
  simp only [d869, h 160 (by decide), agree868 p q h, agree857 p q h]
theorem nonnegative869 (p : Pattern) : 0 ≤ d869 p :=
  nonnegative_ite (p 160) (nonnegative868 p) (nonnegative857 p)
def d870 (p : Pattern) : Int := if p 187 then d59 p else d10 p
theorem agree870 (p q : Pattern) (h : Agree support p q) : d870 p = d870 q := by
  simp only [d870, h 187 (by decide), agree59 p q h, agree10 p q h]
theorem nonnegative870 (p : Pattern) : 0 ≤ d870 p :=
  nonnegative_ite (p 187) (nonnegative59 p) (nonnegative10 p)
def d871 (p : Pattern) : Int := if p 186 then d870 p else d10 p
theorem agree871 (p q : Pattern) (h : Agree support p q) : d871 p = d871 q := by
  simp only [d871, h 186 (by decide), agree870 p q h, agree10 p q h]
theorem nonnegative871 (p : Pattern) : 0 ≤ d871 p :=
  nonnegative_ite (p 186) (nonnegative870 p) (nonnegative10 p)
def d872 (p : Pattern) : Int := if p 168 then d871 p else d864 p
theorem agree872 (p q : Pattern) (h : Agree support p q) : d872 p = d872 q := by
  simp only [d872, h 168 (by decide), agree871 p q h, agree864 p q h]
theorem nonnegative872 (p : Pattern) : 0 ≤ d872 p :=
  nonnegative_ite (p 168) (nonnegative871 p) (nonnegative864 p)
def d873 (p : Pattern) : Int := if p 160 then d868 p else d872 p
theorem agree873 (p q : Pattern) (h : Agree support p q) : d873 p = d873 q := by
  simp only [d873, h 160 (by decide), agree868 p q h, agree872 p q h]
theorem nonnegative873 (p : Pattern) : 0 ≤ d873 p :=
  nonnegative_ite (p 160) (nonnegative868 p) (nonnegative872 p)
def d874 (p : Pattern) : Int := if p 159 then d873 p else d869 p
theorem agree874 (p q : Pattern) (h : Agree support p q) : d874 p = d874 q := by
  simp only [d874, h 159 (by decide), agree873 p q h, agree869 p q h]
theorem nonnegative874 (p : Pattern) : 0 ≤ d874 p :=
  nonnegative_ite (p 159) (nonnegative873 p) (nonnegative869 p)
def d875 (p : Pattern) : Int := if p 158 then d874 p else d869 p
theorem agree875 (p q : Pattern) (h : Agree support p q) : d875 p = d875 q := by
  simp only [d875, h 158 (by decide), agree874 p q h, agree869 p q h]
theorem nonnegative875 (p : Pattern) : 0 ≤ d875 p :=
  nonnegative_ite (p 158) (nonnegative874 p) (nonnegative869 p)
def d876 (p : Pattern) : Int := if p 141 then d875 p else d867 p
theorem agree876 (p q : Pattern) (h : Agree support p q) : d876 p = d876 q := by
  simp only [d876, h 141 (by decide), agree875 p q h, agree867 p q h]
theorem nonnegative876 (p : Pattern) : 0 ≤ d876 p :=
  nonnegative_ite (p 141) (nonnegative875 p) (nonnegative867 p)
def d877 (p : Pattern) : Int := if p 134 then d876 p else d861 p
theorem agree877 (p q : Pattern) (h : Agree support p q) : d877 p = d877 q := by
  simp only [d877, h 134 (by decide), agree876 p q h, agree861 p q h]
theorem nonnegative877 (p : Pattern) : 0 ≤ d877 p :=
  nonnegative_ite (p 134) (nonnegative876 p) (nonnegative861 p)
def d878 (p : Pattern) : Int := if p 158 then d54 p else d856 p
theorem agree878 (p q : Pattern) (h : Agree support p q) : d878 p = d878 q := by
  simp only [d878, h 158 (by decide), agree54 p q h, agree856 p q h]
theorem nonnegative878 (p : Pattern) : 0 ≤ d878 p :=
  nonnegative_ite (p 158) (nonnegative54 p) (nonnegative856 p)
def d879 (p : Pattern) : Int := if p 158 then d868 p else d860 p
theorem agree879 (p q : Pattern) (h : Agree support p q) : d879 p = d879 q := by
  simp only [d879, h 158 (by decide), agree868 p q h, agree860 p q h]
theorem nonnegative879 (p : Pattern) : 0 ≤ d879 p :=
  nonnegative_ite (p 158) (nonnegative868 p) (nonnegative860 p)
def d880 (p : Pattern) : Int := if p 141 then d879 p else d878 p
theorem agree880 (p q : Pattern) (h : Agree support p q) : d880 p = d880 q := by
  simp only [d880, h 141 (by decide), agree879 p q h, agree878 p q h]
theorem nonnegative880 (p : Pattern) : 0 ≤ d880 p :=
  nonnegative_ite (p 141) (nonnegative879 p) (nonnegative878 p)
def d881 (p : Pattern) : Int := if p 158 then d54 p else d866 p
theorem agree881 (p q : Pattern) (h : Agree support p q) : d881 p = d881 q := by
  simp only [d881, h 158 (by decide), agree54 p q h, agree866 p q h]
theorem nonnegative881 (p : Pattern) : 0 ≤ d881 p :=
  nonnegative_ite (p 158) (nonnegative54 p) (nonnegative866 p)
def d882 (p : Pattern) : Int := if p 158 then d868 p else d874 p
theorem agree882 (p q : Pattern) (h : Agree support p q) : d882 p = d882 q := by
  simp only [d882, h 158 (by decide), agree868 p q h, agree874 p q h]
theorem nonnegative882 (p : Pattern) : 0 ≤ d882 p :=
  nonnegative_ite (p 158) (nonnegative868 p) (nonnegative874 p)
def d883 (p : Pattern) : Int := if p 141 then d882 p else d881 p
theorem agree883 (p q : Pattern) (h : Agree support p q) : d883 p = d883 q := by
  simp only [d883, h 141 (by decide), agree882 p q h, agree881 p q h]
theorem nonnegative883 (p : Pattern) : 0 ≤ d883 p :=
  nonnegative_ite (p 141) (nonnegative882 p) (nonnegative881 p)
def d884 (p : Pattern) : Int := if p 134 then d883 p else d880 p
theorem agree884 (p q : Pattern) (h : Agree support p q) : d884 p = d884 q := by
  simp only [d884, h 134 (by decide), agree883 p q h, agree880 p q h]
theorem nonnegative884 (p : Pattern) : 0 ≤ d884 p :=
  nonnegative_ite (p 134) (nonnegative883 p) (nonnegative880 p)
def d885 (p : Pattern) : Int := if p 133 then d884 p else d877 p
theorem agree885 (p q : Pattern) (h : Agree support p q) : d885 p = d885 q := by
  simp only [d885, h 133 (by decide), agree884 p q h, agree877 p q h]
theorem nonnegative885 (p : Pattern) : 0 ≤ d885 p :=
  nonnegative_ite (p 133) (nonnegative884 p) (nonnegative877 p)
def d886 (p : Pattern) : Int := if p 141 then d868 p else d54 p
theorem agree886 (p q : Pattern) (h : Agree support p q) : d886 p = d886 q := by
  simp only [d886, h 141 (by decide), agree868 p q h, agree54 p q h]
theorem nonnegative886 (p : Pattern) : 0 ≤ d886 p :=
  nonnegative_ite (p 141) (nonnegative868 p) (nonnegative54 p)
def d887 (p : Pattern) : Int := if p 133 then d886 p else d884 p
theorem agree887 (p q : Pattern) (h : Agree support p q) : d887 p = d887 q := by
  simp only [d887, h 133 (by decide), agree886 p q h, agree884 p q h]
theorem nonnegative887 (p : Pattern) : 0 ≤ d887 p :=
  nonnegative_ite (p 133) (nonnegative886 p) (nonnegative884 p)
def d888 (p : Pattern) : Int := if p 132 then d887 p else d885 p
theorem agree888 (p q : Pattern) (h : Agree support p q) : d888 p = d888 q := by
  simp only [d888, h 132 (by decide), agree887 p q h, agree885 p q h]
theorem nonnegative888 (p : Pattern) : 0 ≤ d888 p :=
  nonnegative_ite (p 132) (nonnegative887 p) (nonnegative885 p)
def d889 (p : Pattern) : Int := if p 186 then d54 p else d863 p
theorem agree889 (p q : Pattern) (h : Agree support p q) : d889 p = d889 q := by
  simp only [d889, h 186 (by decide), agree54 p q h, agree863 p q h]
theorem nonnegative889 (p : Pattern) : 0 ≤ d889 p :=
  nonnegative_ite (p 186) (nonnegative54 p) (nonnegative863 p)
def d890 (p : Pattern) : Int := if p 160 then d889 p else d864 p
theorem agree890 (p q : Pattern) (h : Agree support p q) : d890 p = d890 q := by
  simp only [d890, h 160 (by decide), agree889 p q h, agree864 p q h]
theorem nonnegative890 (p : Pattern) : 0 ≤ d890 p :=
  nonnegative_ite (p 160) (nonnegative889 p) (nonnegative864 p)
def d891 (p : Pattern) : Int := if p 159 then d890 p else d856 p
theorem agree891 (p q : Pattern) (h : Agree support p q) : d891 p = d891 q := by
  simp only [d891, h 159 (by decide), agree890 p q h, agree856 p q h]
theorem nonnegative891 (p : Pattern) : 0 ≤ d891 p :=
  nonnegative_ite (p 159) (nonnegative890 p) (nonnegative856 p)
def d892 (p : Pattern) : Int := if p 158 then d891 p else d856 p
theorem agree892 (p q : Pattern) (h : Agree support p q) : d892 p = d892 q := by
  simp only [d892, h 158 (by decide), agree891 p q h, agree856 p q h]
theorem nonnegative892 (p : Pattern) : 0 ≤ d892 p :=
  nonnegative_ite (p 158) (nonnegative891 p) (nonnegative856 p)
def d893 (p : Pattern) : Int := if p 186 then d59 p else d870 p
theorem agree893 (p q : Pattern) (h : Agree support p q) : d893 p = d893 q := by
  simp only [d893, h 186 (by decide), agree59 p q h, agree870 p q h]
theorem nonnegative893 (p : Pattern) : 0 ≤ d893 p :=
  nonnegative_ite (p 186) (nonnegative59 p) (nonnegative870 p)
def d894 (p : Pattern) : Int := if p 168 then d893 p else d889 p
theorem agree894 (p q : Pattern) (h : Agree support p q) : d894 p = d894 q := by
  simp only [d894, h 168 (by decide), agree893 p q h, agree889 p q h]
theorem nonnegative894 (p : Pattern) : 0 ≤ d894 p :=
  nonnegative_ite (p 168) (nonnegative893 p) (nonnegative889 p)
def d895 (p : Pattern) : Int := if p 160 then d894 p else d872 p
theorem agree895 (p q : Pattern) (h : Agree support p q) : d895 p = d895 q := by
  simp only [d895, h 160 (by decide), agree894 p q h, agree872 p q h]
theorem nonnegative895 (p : Pattern) : 0 ≤ d895 p :=
  nonnegative_ite (p 160) (nonnegative894 p) (nonnegative872 p)
def d896 (p : Pattern) : Int := if p 159 then d895 p else d860 p
theorem agree896 (p q : Pattern) (h : Agree support p q) : d896 p = d896 q := by
  simp only [d896, h 159 (by decide), agree895 p q h, agree860 p q h]
theorem nonnegative896 (p : Pattern) : 0 ≤ d896 p :=
  nonnegative_ite (p 159) (nonnegative895 p) (nonnegative860 p)
def d897 (p : Pattern) : Int := if p 158 then d896 p else d860 p
theorem agree897 (p q : Pattern) (h : Agree support p q) : d897 p = d897 q := by
  simp only [d897, h 158 (by decide), agree896 p q h, agree860 p q h]
theorem nonnegative897 (p : Pattern) : 0 ≤ d897 p :=
  nonnegative_ite (p 158) (nonnegative896 p) (nonnegative860 p)
def d898 (p : Pattern) : Int := if p 141 then d897 p else d892 p
theorem agree898 (p q : Pattern) (h : Agree support p q) : d898 p = d898 q := by
  simp only [d898, h 141 (by decide), agree897 p q h, agree892 p q h]
theorem nonnegative898 (p : Pattern) : 0 ≤ d898 p :=
  nonnegative_ite (p 141) (nonnegative897 p) (nonnegative892 p)
def d899 (p : Pattern) : Int := if p 134 then d886 p else d898 p
theorem agree899 (p q : Pattern) (h : Agree support p q) : d899 p = d899 q := by
  simp only [d899, h 134 (by decide), agree886 p q h, agree898 p q h]
theorem nonnegative899 (p : Pattern) : 0 ≤ d899 p :=
  nonnegative_ite (p 134) (nonnegative886 p) (nonnegative898 p)
def d900 (p : Pattern) : Int := if p 160 then d889 p else d6 p
theorem agree900 (p q : Pattern) (h : Agree support p q) : d900 p = d900 q := by
  simp only [d900, h 160 (by decide), agree889 p q h, agree6 p q h]
theorem nonnegative900 (p : Pattern) : 0 ≤ d900 p :=
  nonnegative_ite (p 160) (nonnegative889 p) (nonnegative6 p)
def d901 (p : Pattern) : Int := if p 159 then d890 p else d900 p
theorem agree901 (p q : Pattern) (h : Agree support p q) : d901 p = d901 q := by
  simp only [d901, h 159 (by decide), agree890 p q h, agree900 p q h]
theorem nonnegative901 (p : Pattern) : 0 ≤ d901 p :=
  nonnegative_ite (p 159) (nonnegative890 p) (nonnegative900 p)
def d902 (p : Pattern) : Int := if p 158 then d54 p else d901 p
theorem agree902 (p q : Pattern) (h : Agree support p q) : d902 p = d902 q := by
  simp only [d902, h 158 (by decide), agree54 p q h, agree901 p q h]
theorem nonnegative902 (p : Pattern) : 0 ≤ d902 p :=
  nonnegative_ite (p 158) (nonnegative54 p) (nonnegative901 p)
def d903 (p : Pattern) : Int := if p 160 then d894 p else d857 p
theorem agree903 (p q : Pattern) (h : Agree support p q) : d903 p = d903 q := by
  simp only [d903, h 160 (by decide), agree894 p q h, agree857 p q h]
theorem nonnegative903 (p : Pattern) : 0 ≤ d903 p :=
  nonnegative_ite (p 160) (nonnegative894 p) (nonnegative857 p)
def d904 (p : Pattern) : Int := if p 159 then d895 p else d903 p
theorem agree904 (p q : Pattern) (h : Agree support p q) : d904 p = d904 q := by
  simp only [d904, h 159 (by decide), agree895 p q h, agree903 p q h]
theorem nonnegative904 (p : Pattern) : 0 ≤ d904 p :=
  nonnegative_ite (p 159) (nonnegative895 p) (nonnegative903 p)
def d905 (p : Pattern) : Int := if p 158 then d868 p else d904 p
theorem agree905 (p q : Pattern) (h : Agree support p q) : d905 p = d905 q := by
  simp only [d905, h 158 (by decide), agree868 p q h, agree904 p q h]
theorem nonnegative905 (p : Pattern) : 0 ≤ d905 p :=
  nonnegative_ite (p 158) (nonnegative868 p) (nonnegative904 p)
def d906 (p : Pattern) : Int := if p 141 then d905 p else d902 p
theorem agree906 (p q : Pattern) (h : Agree support p q) : d906 p = d906 q := by
  simp only [d906, h 141 (by decide), agree905 p q h, agree902 p q h]
theorem nonnegative906 (p : Pattern) : 0 ≤ d906 p :=
  nonnegative_ite (p 141) (nonnegative905 p) (nonnegative902 p)
def d907 (p : Pattern) : Int := if p 134 then d886 p else d906 p
theorem agree907 (p q : Pattern) (h : Agree support p q) : d907 p = d907 q := by
  simp only [d907, h 134 (by decide), agree886 p q h, agree906 p q h]
theorem nonnegative907 (p : Pattern) : 0 ≤ d907 p :=
  nonnegative_ite (p 134) (nonnegative886 p) (nonnegative906 p)
def d908 (p : Pattern) : Int := if p 133 then d907 p else d899 p
theorem agree908 (p q : Pattern) (h : Agree support p q) : d908 p = d908 q := by
  simp only [d908, h 133 (by decide), agree907 p q h, agree899 p q h]
theorem nonnegative908 (p : Pattern) : 0 ≤ d908 p :=
  nonnegative_ite (p 133) (nonnegative907 p) (nonnegative899 p)
def d909 (p : Pattern) : Int := if p 158 then d54 p else d891 p
theorem agree909 (p q : Pattern) (h : Agree support p q) : d909 p = d909 q := by
  simp only [d909, h 158 (by decide), agree54 p q h, agree891 p q h]
theorem nonnegative909 (p : Pattern) : 0 ≤ d909 p :=
  nonnegative_ite (p 158) (nonnegative54 p) (nonnegative891 p)
def d910 (p : Pattern) : Int := if p 158 then d868 p else d896 p
theorem agree910 (p q : Pattern) (h : Agree support p q) : d910 p = d910 q := by
  simp only [d910, h 158 (by decide), agree868 p q h, agree896 p q h]
theorem nonnegative910 (p : Pattern) : 0 ≤ d910 p :=
  nonnegative_ite (p 158) (nonnegative868 p) (nonnegative896 p)
def d911 (p : Pattern) : Int := if p 141 then d910 p else d909 p
theorem agree911 (p q : Pattern) (h : Agree support p q) : d911 p = d911 q := by
  simp only [d911, h 141 (by decide), agree910 p q h, agree909 p q h]
theorem nonnegative911 (p : Pattern) : 0 ≤ d911 p :=
  nonnegative_ite (p 141) (nonnegative910 p) (nonnegative909 p)
def d912 (p : Pattern) : Int := if p 134 then d886 p else d911 p
theorem agree912 (p q : Pattern) (h : Agree support p q) : d912 p = d912 q := by
  simp only [d912, h 134 (by decide), agree886 p q h, agree911 p q h]
theorem nonnegative912 (p : Pattern) : 0 ≤ d912 p :=
  nonnegative_ite (p 134) (nonnegative886 p) (nonnegative911 p)
def d913 (p : Pattern) : Int := if p 133 then d886 p else d912 p
theorem agree913 (p q : Pattern) (h : Agree support p q) : d913 p = d913 q := by
  simp only [d913, h 133 (by decide), agree886 p q h, agree912 p q h]
theorem nonnegative913 (p : Pattern) : 0 ≤ d913 p :=
  nonnegative_ite (p 133) (nonnegative886 p) (nonnegative912 p)
def d914 (p : Pattern) : Int := if p 132 then d913 p else d908 p
theorem agree914 (p q : Pattern) (h : Agree support p q) : d914 p = d914 q := by
  simp only [d914, h 132 (by decide), agree913 p q h, agree908 p q h]
theorem nonnegative914 (p : Pattern) : 0 ≤ d914 p :=
  nonnegative_ite (p 132) (nonnegative913 p) (nonnegative908 p)
def d915 (p : Pattern) : Int := if p 108 then d914 p else d888 p
theorem agree915 (p q : Pattern) (h : Agree support p q) : d915 p = d915 q := by
  simp only [d915, h 108 (by decide), agree914 p q h, agree888 p q h]
theorem nonnegative915 (p : Pattern) : 0 ≤ d915 p :=
  nonnegative_ite (p 108) (nonnegative914 p) (nonnegative888 p)
def d916 (p : Pattern) : Int := if p 193 then d1 p else d0 p
theorem agree916 (p q : Pattern) (h : Agree support p q) : d916 p = d916 q := by
  simp only [d916, h 193 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative916 (p : Pattern) : 0 ≤ d916 p :=
  nonnegative_ite (p 193) (nonnegative1 p) (nonnegative0 p)
def d917 (p : Pattern) : Int := if p 193 then d0 p else d1 p
theorem agree917 (p q : Pattern) (h : Agree support p q) : d917 p = d917 q := by
  simp only [d917, h 193 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative917 (p : Pattern) : 0 ≤ d917 p :=
  nonnegative_ite (p 193) (nonnegative0 p) (nonnegative1 p)
def d918 (p : Pattern) : Int := if p 141 then d0 p else d917 p
theorem agree918 (p q : Pattern) (h : Agree support p q) : d918 p = d918 q := by
  simp only [d918, h 141 (by decide), agree0 p q h, agree917 p q h]
theorem nonnegative918 (p : Pattern) : 0 ≤ d918 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative917 p)
def d919 (p : Pattern) : Int := if p 192 then d2 p else d0 p
theorem agree919 (p q : Pattern) (h : Agree support p q) : d919 p = d919 q := by
  simp only [d919, h 192 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative919 (p : Pattern) : 0 ≤ d919 p :=
  nonnegative_ite (p 192) (nonnegative2 p) (nonnegative0 p)
def d920 (p : Pattern) : Int := if p 192 then d4 p else d2 p
theorem agree920 (p q : Pattern) (h : Agree support p q) : d920 p = d920 q := by
  simp only [d920, h 192 (by decide), agree4 p q h, agree2 p q h]
theorem nonnegative920 (p : Pattern) : 0 ≤ d920 p :=
  nonnegative_ite (p 192) (nonnegative4 p) (nonnegative2 p)
def d921 (p : Pattern) : Int := if p 186 then d920 p else d919 p
theorem agree921 (p q : Pattern) (h : Agree support p q) : d921 p = d921 q := by
  simp only [d921, h 186 (by decide), agree920 p q h, agree919 p q h]
theorem nonnegative921 (p : Pattern) : 0 ≤ d921 p :=
  nonnegative_ite (p 186) (nonnegative920 p) (nonnegative919 p)
def d922 (p : Pattern) : Int := if p 160 then d921 p else d919 p
theorem agree922 (p q : Pattern) (h : Agree support p q) : d922 p = d922 q := by
  simp only [d922, h 160 (by decide), agree921 p q h, agree919 p q h]
theorem nonnegative922 (p : Pattern) : 0 ≤ d922 p :=
  nonnegative_ite (p 160) (nonnegative921 p) (nonnegative919 p)
def d923 (p : Pattern) : Int := if p 192 then d9 p else d8 p
theorem agree923 (p q : Pattern) (h : Agree support p q) : d923 p = d923 q := by
  simp only [d923, h 192 (by decide), agree9 p q h, agree8 p q h]
theorem nonnegative923 (p : Pattern) : 0 ≤ d923 p :=
  nonnegative_ite (p 192) (nonnegative9 p) (nonnegative8 p)
def d924 (p : Pattern) : Int := if p 168 then d923 p else d919 p
theorem agree924 (p q : Pattern) (h : Agree support p q) : d924 p = d924 q := by
  simp only [d924, h 168 (by decide), agree923 p q h, agree919 p q h]
theorem nonnegative924 (p : Pattern) : 0 ≤ d924 p :=
  nonnegative_ite (p 168) (nonnegative923 p) (nonnegative919 p)
def d925 (p : Pattern) : Int := if p 192 then d58 p else d9 p
theorem agree925 (p q : Pattern) (h : Agree support p q) : d925 p = d925 q := by
  simp only [d925, h 192 (by decide), agree58 p q h, agree9 p q h]
theorem nonnegative925 (p : Pattern) : 0 ≤ d925 p :=
  nonnegative_ite (p 192) (nonnegative58 p) (nonnegative9 p)
def d926 (p : Pattern) : Int := if p 186 then d925 p else d923 p
theorem agree926 (p q : Pattern) (h : Agree support p q) : d926 p = d926 q := by
  simp only [d926, h 186 (by decide), agree925 p q h, agree923 p q h]
theorem nonnegative926 (p : Pattern) : 0 ≤ d926 p :=
  nonnegative_ite (p 186) (nonnegative925 p) (nonnegative923 p)
def d927 (p : Pattern) : Int := if p 168 then d926 p else d921 p
theorem agree927 (p q : Pattern) (h : Agree support p q) : d927 p = d927 q := by
  simp only [d927, h 168 (by decide), agree926 p q h, agree921 p q h]
theorem nonnegative927 (p : Pattern) : 0 ≤ d927 p :=
  nonnegative_ite (p 168) (nonnegative926 p) (nonnegative921 p)
def d928 (p : Pattern) : Int := if p 160 then d927 p else d924 p
theorem agree928 (p q : Pattern) (h : Agree support p q) : d928 p = d928 q := by
  simp only [d928, h 160 (by decide), agree927 p q h, agree924 p q h]
theorem nonnegative928 (p : Pattern) : 0 ≤ d928 p :=
  nonnegative_ite (p 160) (nonnegative927 p) (nonnegative924 p)
def d929 (p : Pattern) : Int := if p 141 then d928 p else d922 p
theorem agree929 (p q : Pattern) (h : Agree support p q) : d929 p = d929 q := by
  simp only [d929, h 141 (by decide), agree928 p q h, agree922 p q h]
theorem nonnegative929 (p : Pattern) : 0 ≤ d929 p :=
  nonnegative_ite (p 141) (nonnegative928 p) (nonnegative922 p)
def d930 (p : Pattern) : Int := if p 160 then d920 p else d919 p
theorem agree930 (p q : Pattern) (h : Agree support p q) : d930 p = d930 q := by
  simp only [d930, h 160 (by decide), agree920 p q h, agree919 p q h]
theorem nonnegative930 (p : Pattern) : 0 ≤ d930 p :=
  nonnegative_ite (p 160) (nonnegative920 p) (nonnegative919 p)
def d931 (p : Pattern) : Int := if p 187 then d920 p else d919 p
theorem agree931 (p q : Pattern) (h : Agree support p q) : d931 p = d931 q := by
  simp only [d931, h 187 (by decide), agree920 p q h, agree919 p q h]
theorem nonnegative931 (p : Pattern) : 0 ≤ d931 p :=
  nonnegative_ite (p 187) (nonnegative920 p) (nonnegative919 p)
def d932 (p : Pattern) : Int := if p 186 then d931 p else d919 p
theorem agree932 (p q : Pattern) (h : Agree support p q) : d932 p = d932 q := by
  simp only [d932, h 186 (by decide), agree931 p q h, agree919 p q h]
theorem nonnegative932 (p : Pattern) : 0 ≤ d932 p :=
  nonnegative_ite (p 186) (nonnegative931 p) (nonnegative919 p)
def d933 (p : Pattern) : Int := if p 160 then d920 p else d932 p
theorem agree933 (p q : Pattern) (h : Agree support p q) : d933 p = d933 q := by
  simp only [d933, h 160 (by decide), agree920 p q h, agree932 p q h]
theorem nonnegative933 (p : Pattern) : 0 ≤ d933 p :=
  nonnegative_ite (p 160) (nonnegative920 p) (nonnegative932 p)
def d934 (p : Pattern) : Int := if p 159 then d933 p else d930 p
theorem agree934 (p q : Pattern) (h : Agree support p q) : d934 p = d934 q := by
  simp only [d934, h 159 (by decide), agree933 p q h, agree930 p q h]
theorem nonnegative934 (p : Pattern) : 0 ≤ d934 p :=
  nonnegative_ite (p 159) (nonnegative933 p) (nonnegative930 p)
def d935 (p : Pattern) : Int := if p 158 then d934 p else d930 p
theorem agree935 (p q : Pattern) (h : Agree support p q) : d935 p = d935 q := by
  simp only [d935, h 158 (by decide), agree934 p q h, agree930 p q h]
theorem nonnegative935 (p : Pattern) : 0 ≤ d935 p :=
  nonnegative_ite (p 158) (nonnegative934 p) (nonnegative930 p)
def d936 (p : Pattern) : Int := if p 168 then d925 p else d920 p
theorem agree936 (p q : Pattern) (h : Agree support p q) : d936 p = d936 q := by
  simp only [d936, h 168 (by decide), agree925 p q h, agree920 p q h]
theorem nonnegative936 (p : Pattern) : 0 ≤ d936 p :=
  nonnegative_ite (p 168) (nonnegative925 p) (nonnegative920 p)
def d937 (p : Pattern) : Int := if p 160 then d936 p else d924 p
theorem agree937 (p q : Pattern) (h : Agree support p q) : d937 p = d937 q := by
  simp only [d937, h 160 (by decide), agree936 p q h, agree924 p q h]
theorem nonnegative937 (p : Pattern) : 0 ≤ d937 p :=
  nonnegative_ite (p 160) (nonnegative936 p) (nonnegative924 p)
def d938 (p : Pattern) : Int := if p 187 then d925 p else d923 p
theorem agree938 (p q : Pattern) (h : Agree support p q) : d938 p = d938 q := by
  simp only [d938, h 187 (by decide), agree925 p q h, agree923 p q h]
theorem nonnegative938 (p : Pattern) : 0 ≤ d938 p :=
  nonnegative_ite (p 187) (nonnegative925 p) (nonnegative923 p)
def d939 (p : Pattern) : Int := if p 186 then d938 p else d923 p
theorem agree939 (p q : Pattern) (h : Agree support p q) : d939 p = d939 q := by
  simp only [d939, h 186 (by decide), agree938 p q h, agree923 p q h]
theorem nonnegative939 (p : Pattern) : 0 ≤ d939 p :=
  nonnegative_ite (p 186) (nonnegative938 p) (nonnegative923 p)
def d940 (p : Pattern) : Int := if p 168 then d939 p else d932 p
theorem agree940 (p q : Pattern) (h : Agree support p q) : d940 p = d940 q := by
  simp only [d940, h 168 (by decide), agree939 p q h, agree932 p q h]
theorem nonnegative940 (p : Pattern) : 0 ≤ d940 p :=
  nonnegative_ite (p 168) (nonnegative939 p) (nonnegative932 p)
def d941 (p : Pattern) : Int := if p 160 then d936 p else d940 p
theorem agree941 (p q : Pattern) (h : Agree support p q) : d941 p = d941 q := by
  simp only [d941, h 160 (by decide), agree936 p q h, agree940 p q h]
theorem nonnegative941 (p : Pattern) : 0 ≤ d941 p :=
  nonnegative_ite (p 160) (nonnegative936 p) (nonnegative940 p)
def d942 (p : Pattern) : Int := if p 159 then d941 p else d937 p
theorem agree942 (p q : Pattern) (h : Agree support p q) : d942 p = d942 q := by
  simp only [d942, h 159 (by decide), agree941 p q h, agree937 p q h]
theorem nonnegative942 (p : Pattern) : 0 ≤ d942 p :=
  nonnegative_ite (p 159) (nonnegative941 p) (nonnegative937 p)
def d943 (p : Pattern) : Int := if p 158 then d942 p else d937 p
theorem agree943 (p q : Pattern) (h : Agree support p q) : d943 p = d943 q := by
  simp only [d943, h 158 (by decide), agree942 p q h, agree937 p q h]
theorem nonnegative943 (p : Pattern) : 0 ≤ d943 p :=
  nonnegative_ite (p 158) (nonnegative942 p) (nonnegative937 p)
def d944 (p : Pattern) : Int := if p 141 then d943 p else d935 p
theorem agree944 (p q : Pattern) (h : Agree support p q) : d944 p = d944 q := by
  simp only [d944, h 141 (by decide), agree943 p q h, agree935 p q h]
theorem nonnegative944 (p : Pattern) : 0 ≤ d944 p :=
  nonnegative_ite (p 141) (nonnegative943 p) (nonnegative935 p)
def d945 (p : Pattern) : Int := if p 134 then d944 p else d929 p
theorem agree945 (p q : Pattern) (h : Agree support p q) : d945 p = d945 q := by
  simp only [d945, h 134 (by decide), agree944 p q h, agree929 p q h]
theorem nonnegative945 (p : Pattern) : 0 ≤ d945 p :=
  nonnegative_ite (p 134) (nonnegative944 p) (nonnegative929 p)
def d946 (p : Pattern) : Int := if p 158 then d920 p else d922 p
theorem agree946 (p q : Pattern) (h : Agree support p q) : d946 p = d946 q := by
  simp only [d946, h 158 (by decide), agree920 p q h, agree922 p q h]
theorem nonnegative946 (p : Pattern) : 0 ≤ d946 p :=
  nonnegative_ite (p 158) (nonnegative920 p) (nonnegative922 p)
def d947 (p : Pattern) : Int := if p 158 then d936 p else d928 p
theorem agree947 (p q : Pattern) (h : Agree support p q) : d947 p = d947 q := by
  simp only [d947, h 158 (by decide), agree936 p q h, agree928 p q h]
theorem nonnegative947 (p : Pattern) : 0 ≤ d947 p :=
  nonnegative_ite (p 158) (nonnegative936 p) (nonnegative928 p)
def d948 (p : Pattern) : Int := if p 141 then d947 p else d946 p
theorem agree948 (p q : Pattern) (h : Agree support p q) : d948 p = d948 q := by
  simp only [d948, h 141 (by decide), agree947 p q h, agree946 p q h]
theorem nonnegative948 (p : Pattern) : 0 ≤ d948 p :=
  nonnegative_ite (p 141) (nonnegative947 p) (nonnegative946 p)
def d949 (p : Pattern) : Int := if p 158 then d920 p else d934 p
theorem agree949 (p q : Pattern) (h : Agree support p q) : d949 p = d949 q := by
  simp only [d949, h 158 (by decide), agree920 p q h, agree934 p q h]
theorem nonnegative949 (p : Pattern) : 0 ≤ d949 p :=
  nonnegative_ite (p 158) (nonnegative920 p) (nonnegative934 p)
def d950 (p : Pattern) : Int := if p 158 then d936 p else d942 p
theorem agree950 (p q : Pattern) (h : Agree support p q) : d950 p = d950 q := by
  simp only [d950, h 158 (by decide), agree936 p q h, agree942 p q h]
theorem nonnegative950 (p : Pattern) : 0 ≤ d950 p :=
  nonnegative_ite (p 158) (nonnegative936 p) (nonnegative942 p)
def d951 (p : Pattern) : Int := if p 141 then d950 p else d949 p
theorem agree951 (p q : Pattern) (h : Agree support p q) : d951 p = d951 q := by
  simp only [d951, h 141 (by decide), agree950 p q h, agree949 p q h]
theorem nonnegative951 (p : Pattern) : 0 ≤ d951 p :=
  nonnegative_ite (p 141) (nonnegative950 p) (nonnegative949 p)
def d952 (p : Pattern) : Int := if p 134 then d951 p else d948 p
theorem agree952 (p q : Pattern) (h : Agree support p q) : d952 p = d952 q := by
  simp only [d952, h 134 (by decide), agree951 p q h, agree948 p q h]
theorem nonnegative952 (p : Pattern) : 0 ≤ d952 p :=
  nonnegative_ite (p 134) (nonnegative951 p) (nonnegative948 p)
def d953 (p : Pattern) : Int := if p 133 then d952 p else d945 p
theorem agree953 (p q : Pattern) (h : Agree support p q) : d953 p = d953 q := by
  simp only [d953, h 133 (by decide), agree952 p q h, agree945 p q h]
theorem nonnegative953 (p : Pattern) : 0 ≤ d953 p :=
  nonnegative_ite (p 133) (nonnegative952 p) (nonnegative945 p)
def d954 (p : Pattern) : Int := if p 141 then d936 p else d920 p
theorem agree954 (p q : Pattern) (h : Agree support p q) : d954 p = d954 q := by
  simp only [d954, h 141 (by decide), agree936 p q h, agree920 p q h]
theorem nonnegative954 (p : Pattern) : 0 ≤ d954 p :=
  nonnegative_ite (p 141) (nonnegative936 p) (nonnegative920 p)
def d955 (p : Pattern) : Int := if p 133 then d954 p else d952 p
theorem agree955 (p q : Pattern) (h : Agree support p q) : d955 p = d955 q := by
  simp only [d955, h 133 (by decide), agree954 p q h, agree952 p q h]
theorem nonnegative955 (p : Pattern) : 0 ≤ d955 p :=
  nonnegative_ite (p 133) (nonnegative954 p) (nonnegative952 p)
def d956 (p : Pattern) : Int := if p 132 then d955 p else d953 p
theorem agree956 (p q : Pattern) (h : Agree support p q) : d956 p = d956 q := by
  simp only [d956, h 132 (by decide), agree955 p q h, agree953 p q h]
theorem nonnegative956 (p : Pattern) : 0 ≤ d956 p :=
  nonnegative_ite (p 132) (nonnegative955 p) (nonnegative953 p)
def d957 (p : Pattern) : Int := if p 186 then d920 p else d931 p
theorem agree957 (p q : Pattern) (h : Agree support p q) : d957 p = d957 q := by
  simp only [d957, h 186 (by decide), agree920 p q h, agree931 p q h]
theorem nonnegative957 (p : Pattern) : 0 ≤ d957 p :=
  nonnegative_ite (p 186) (nonnegative920 p) (nonnegative931 p)
def d958 (p : Pattern) : Int := if p 160 then d957 p else d932 p
theorem agree958 (p q : Pattern) (h : Agree support p q) : d958 p = d958 q := by
  simp only [d958, h 160 (by decide), agree957 p q h, agree932 p q h]
theorem nonnegative958 (p : Pattern) : 0 ≤ d958 p :=
  nonnegative_ite (p 160) (nonnegative957 p) (nonnegative932 p)
def d959 (p : Pattern) : Int := if p 159 then d958 p else d922 p
theorem agree959 (p q : Pattern) (h : Agree support p q) : d959 p = d959 q := by
  simp only [d959, h 159 (by decide), agree958 p q h, agree922 p q h]
theorem nonnegative959 (p : Pattern) : 0 ≤ d959 p :=
  nonnegative_ite (p 159) (nonnegative958 p) (nonnegative922 p)
end NetHack.Sokoban12CostPartition
