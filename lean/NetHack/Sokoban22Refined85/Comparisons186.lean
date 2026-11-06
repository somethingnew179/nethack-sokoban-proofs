/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons185
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26040 (p : Pattern) (guard : d5843 p = 1) : d3001 p ≤ (0 : Int) + d3761 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3001, d3761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26037 p hg
    simpa only [d3001, d3761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3001, d3761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26039 p hg
    simpa only [d3001, d3761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26041 (p : Pattern) (guard : d5843 p = 1) : d1945 p ≤ (0 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1945, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d1945, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1945, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20207 p hg
    simpa only [d5843, d1945, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26042 (p : Pattern) (guard : d5843 p = 1) : d1946 p ≤ (0 : Int) + d3762 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1946, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26041 p hg
    simpa only [d1946, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1946, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d1946, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26043 (p : Pattern) (guard : d5843 p = 1) : d1947 p ≤ (0 : Int) + d3763 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1947, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d1947, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1947, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26042 p hg
    simpa only [d1947, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26044 (p : Pattern) (guard : d5843 p = 1) : d1955 p ≤ (0 : Int) + d1955 p := by
  omega
theorem compare26045 (p : Pattern) (guard : d5843 p = 1) : d1956 p ≤ (0 : Int) + d3764 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1956, d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d1956, d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1956, d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26044 p hg
    simpa only [d1956, d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26046 (p : Pattern) (guard : d5843 p = 1) : d1957 p ≤ (0 : Int) + d3765 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1957, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26043 p hg
    simpa only [d1957, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1957, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26045 p hg
    simpa only [d1957, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26047 (p : Pattern) (guard : d5843 p = 1) : d3002 p ≤ (0 : Int) + d3766 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3002, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d3002, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3002, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26046 p hg
    simpa only [d3002, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26048 (p : Pattern) (guard : d5843 p = 1) : d1891 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1891, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d1891, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1891, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19887 p hg
    simpa only [d5843, d1891, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26049 (p : Pattern) (guard : d5843 p = 1) : d1892 p ≤ (0 : Int) + d3767 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1892, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26048 p hg
    simpa only [d1892, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1892, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d1892, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26050 (p : Pattern) (guard : d5843 p = 1) : d1893 p ≤ (0 : Int) + d3768 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1893, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d1893, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1893, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26049 p hg
    simpa only [d1893, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26051 (p : Pattern) (guard : d5843 p = 1) : d1896 p ≤ (0 : Int) + d1896 p := by
  omega
theorem compare26052 (p : Pattern) (guard : d5843 p = 1) : d1897 p ≤ (0 : Int) + d3770 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1897, d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d1897, d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1897, d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26051 p hg
    simpa only [d1897, d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26053 (p : Pattern) (guard : d5843 p = 1) : d1898 p ≤ (0 : Int) + d3771 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1898, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26050 p hg
    simpa only [d1898, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1898, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26052 p hg
    simpa only [d1898, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26054 (p : Pattern) (guard : d5843 p = 1) : d1899 p ≤ (0 : Int) + d3772 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1899, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26053 p hg
    simpa only [d1899, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1899, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1899, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26055 (p : Pattern) (guard : d5843 p = 1) : d3003 p ≤ (0 : Int) + d3773 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3003, d3773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26047 p hg
    simpa only [d3003, d3773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3003, d3773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26054 p hg
    simpa only [d3003, d3773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26056 (p : Pattern) (guard : d5843 p = 1) : d317 p ≤ (0 : Int) + d317 p := by
  omega
theorem compare26057 (p : Pattern) (guard : d5843 p = 1) : d1901 p ≤ (0 : Int) + d3774 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1901, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20210 p hg
    simpa only [d1901, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1901, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26056 p hg
    simpa only [d1901, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26058 (p : Pattern) (guard : d5843 p = 1) : d1904 p ≤ (0 : Int) + d3776 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1904, d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20806 p hg
    simpa only [d1904, d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1904, d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26056 p hg
    simpa only [d1904, d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26059 (p : Pattern) (guard : d5843 p = 1) : d1905 p ≤ (0 : Int) + d3777 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1905, d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26057 p hg
    simpa only [d1905, d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1905, d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26058 p hg
    simpa only [d1905, d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26060 (p : Pattern) (guard : d5843 p = 1) : d1906 p ≤ (0 : Int) + d3778 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1906, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26059 p hg
    simpa only [d1906, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1906, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1906, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26061 (p : Pattern) (guard : d5843 p = 1) : d3004 p ≤ (0 : Int) + d3779 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3004, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26047 p hg
    simpa only [d3004, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3004, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26060 p hg
    simpa only [d3004, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26062 (p : Pattern) (guard : d5843 p = 1) : d3005 p ≤ (0 : Int) + d3780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3005, d3780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26055 p hg
    simpa only [d3005, d3780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3005, d3780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26061 p hg
    simpa only [d3005, d3780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26063 (p : Pattern) (guard : d5843 p = 1) : d3006 p ≤ (0 : Int) + d3781 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3006, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26047 p hg
    simpa only [d3006, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3006, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3006, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26064 (p : Pattern) (guard : d5843 p = 1) : d1960 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1960, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d1960, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1960, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d1960, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26065 (p : Pattern) (guard : d5843 p = 1) : d1961 p ≤ (0 : Int) + d3782 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1961, d3782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26064 p hg
    simpa only [d1961, d3782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1961, d3782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d1961, d3782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26066 (p : Pattern) (guard : d5843 p = 1) : d1962 p ≤ (0 : Int) + d3783 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1962, d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d1962, d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1962, d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26065 p hg
    simpa only [d1962, d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26067 (p : Pattern) (guard : d5843 p = 1) : d348 p ≤ (0 : Int) + d348 p := by
  omega
theorem compare26068 (p : Pattern) (guard : d5843 p = 1) : d1965 p ≤ (0 : Int) + d3784 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1965, d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20772 p hg
    simpa only [d1965, d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1965, d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26067 p hg
    simpa only [d1965, d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26069 (p : Pattern) (guard : d5843 p = 1) : d1966 p ≤ (0 : Int) + d3785 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1966, d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26066 p hg
    simpa only [d1966, d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1966, d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26068 p hg
    simpa only [d1966, d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26070 (p : Pattern) (guard : d5843 p = 1) : d3007 p ≤ (0 : Int) + d3786 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3007, d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d3007, d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3007, d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26069 p hg
    simpa only [d3007, d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26071 (p : Pattern) (guard : d5843 p = 1) : d3008 p ≤ (0 : Int) + d3787 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3008, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26070 p hg
    simpa only [d3008, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3008, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3008, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26072 (p : Pattern) (guard : d5843 p = 1) : d3009 p ≤ (0 : Int) + d3788 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3009, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26063 p hg
    simpa only [d3009, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3009, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26071 p hg
    simpa only [d3009, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26073 (p : Pattern) (guard : d5843 p = 1) : d3010 p ≤ (0 : Int) + d3789 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3010, d3789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26062 p hg
    simpa only [d3010, d3789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3010, d3789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26072 p hg
    simpa only [d3010, d3789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26074 (p : Pattern) (guard : d5843 p = 1) : d3011 p ≤ (0 : Int) + d3790 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3011, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25927 p hg
    simpa only [d3011, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3011, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3011, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26075 (p : Pattern) (guard : d5843 p = 1) : d3012 p ≤ (0 : Int) + d3791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3012, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26072 p hg
    simpa only [d3012, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3012, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26074 p hg
    simpa only [d3012, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26076 (p : Pattern) (guard : d5843 p = 1) : d3013 p ≤ (0 : Int) + d3792 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3013, d3792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26073 p hg
    simpa only [d3013, d3792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3013, d3792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26075 p hg
    simpa only [d3013, d3792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26077 (p : Pattern) (guard : d5843 p = 1) : d3014 p ≤ (0 : Int) + d3793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3014, d3793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26040 p hg
    simpa only [d3014, d3793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3014, d3793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26076 p hg
    simpa only [d3014, d3793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26078 (p : Pattern) (guard : d5843 p = 1) : d2124 p ≤ (0 : Int) + d3794 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2124, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d2124, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2124, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d2124, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26079 (p : Pattern) (guard : d5843 p = 1) : d2125 p ≤ (0 : Int) + d3795 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2125, d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26078 p hg
    simpa only [d2125, d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2125, d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d2125, d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26080 (p : Pattern) (guard : d5843 p = 1) : d3015 p ≤ (0 : Int) + d3796 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3015, d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d3015, d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3015, d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26079 p hg
    simpa only [d3015, d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26081 (p : Pattern) (guard : d5843 p = 1) : d1920 p ≤ (0 : Int) + d3798 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1920, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d1920, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1920, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20838 p hg
    simpa only [d1920, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26082 (p : Pattern) (guard : d5843 p = 1) : d1921 p ≤ (0 : Int) + d3799 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1921, d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26081 p hg
    simpa only [d1921, d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1921, d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20838 p hg
    simpa only [d1921, d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26083 (p : Pattern) (guard : d5843 p = 1) : d1922 p ≤ (0 : Int) + d3800 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1922, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26082 p hg
    simpa only [d1922, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1922, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1922, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26084 (p : Pattern) (guard : d5843 p = 1) : d3016 p ≤ (0 : Int) + d3801 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3016, d3801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26080 p hg
    simpa only [d3016, d3801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3016, d3801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26083 p hg
    simpa only [d3016, d3801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26085 (p : Pattern) (guard : d5843 p = 1) : d3017 p ≤ (0 : Int) + d3802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3017, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26027 p hg
    simpa only [d3017, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3017, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26084 p hg
    simpa only [d3017, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26086 (p : Pattern) (guard : d5843 p = 1) : d3018 p ≤ (0 : Int) + d3803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3018, d3803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26035 p hg
    simpa only [d3018, d3803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3018, d3803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25915 p hg
    simpa only [d3018, d3803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26087 (p : Pattern) (guard : d5843 p = 1) : d3019 p ≤ (0 : Int) + d3804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3019, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26085 p hg
    simpa only [d3019, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3019, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26086 p hg
    simpa only [d3019, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26088 (p : Pattern) (guard : d5843 p = 1) : d3020 p ≤ (0 : Int) + d3805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3020, d3805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26035 p hg
    simpa only [d3020, d3805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3020, d3805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25918 p hg
    simpa only [d3020, d3805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26089 (p : Pattern) (guard : d5843 p = 1) : d3021 p ≤ (0 : Int) + d3806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3021, d3806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26088 p hg
    simpa only [d3021, d3806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3021, d3806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3021, d3806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26090 (p : Pattern) (guard : d5843 p = 1) : d3022 p ≤ (0 : Int) + d3807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3022, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26087 p hg
    simpa only [d3022, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3022, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26089 p hg
    simpa only [d3022, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26091 (p : Pattern) (guard : d5843 p = 1) : d3023 p ≤ (0 : Int) + d3808 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3023, d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d3023, d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3023, d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26053 p hg
    simpa only [d3023, d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26092 (p : Pattern) (guard : d5843 p = 1) : d3024 p ≤ (0 : Int) + d3809 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3024, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26091 p hg
    simpa only [d3024, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3024, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3024, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26093 (p : Pattern) (guard : d5843 p = 1) : d3025 p ≤ (0 : Int) + d3810 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3025, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26061 p hg
    simpa only [d3025, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3025, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26092 p hg
    simpa only [d3025, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26094 (p : Pattern) (guard : d5843 p = 1) : d3026 p ≤ (0 : Int) + d3811 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3026, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26071 p hg
    simpa only [d3026, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3026, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25927 p hg
    simpa only [d3026, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26095 (p : Pattern) (guard : d5843 p = 1) : d3027 p ≤ (0 : Int) + d3812 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3027, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26093 p hg
    simpa only [d3027, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3027, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26094 p hg
    simpa only [d3027, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26096 (p : Pattern) (guard : d5843 p = 1) : d3028 p ≤ (0 : Int) + d3813 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3028, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26071 p hg
    simpa only [d3028, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3028, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25929 p hg
    simpa only [d3028, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26097 (p : Pattern) (guard : d5843 p = 1) : d3029 p ≤ (0 : Int) + d3814 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3029, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26096 p hg
    simpa only [d3029, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3029, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3029, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26098 (p : Pattern) (guard : d5843 p = 1) : d3030 p ≤ (0 : Int) + d3815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3030, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26095 p hg
    simpa only [d3030, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3030, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26097 p hg
    simpa only [d3030, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26099 (p : Pattern) (guard : d5843 p = 1) : d3031 p ≤ (0 : Int) + d3816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3031, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26090 p hg
    simpa only [d3031, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3031, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26098 p hg
    simpa only [d3031, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26100 (p : Pattern) (guard : d5843 p = 1) : d3032 p ≤ (0 : Int) + d3817 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3032, d3817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26077 p hg
    simpa only [d3032, d3817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3032, d3817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26099 p hg
    simpa only [d3032, d3817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26101 (p : Pattern) (guard : d5843 p = 1) : d2107 p ≤ (0 : Int) + d3818 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2107, d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d2107, d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2107, d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26042 p hg
    simpa only [d2107, d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26102 (p : Pattern) (guard : d5843 p = 1) : d2108 p ≤ (0 : Int) + d3819 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2108, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26043 p hg
    simpa only [d2108, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2108, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26101 p hg
    simpa only [d2108, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26103 (p : Pattern) (guard : d5843 p = 1) : d3033 p ≤ (0 : Int) + d3820 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3033, d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d3033, d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3033, d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26102 p hg
    simpa only [d3033, d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26104 (p : Pattern) (guard : d5843 p = 1) : d1943 p ≤ (0 : Int) + d3821 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1943, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26020 p hg
    simpa only [d1943, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1943, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1943, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26105 (p : Pattern) (guard : d5843 p = 1) : d3034 p ≤ (0 : Int) + d3822 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3034, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26103 p hg
    simpa only [d3034, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3034, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26104 p hg
    simpa only [d3034, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26106 (p : Pattern) (guard : d5843 p = 1) : d3035 p ≤ (0 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d3035, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d3035, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d3035, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d3035, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26107 (p : Pattern) (guard : d5843 p = 1) : d3036 p ≤ (0 : Int) + d1955 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3036, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26106 p hg
    simpa only [d3036, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3036, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d3036, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26108 (p : Pattern) (guard : d5843 p = 1) : d3037 p ≤ (0 : Int) + d3764 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3037, d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d3037, d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3037, d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26107 p hg
    simpa only [d3037, d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26109 (p : Pattern) (guard : d5843 p = 1) : d3038 p ≤ (0 : Int) + d3765 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3038, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26043 p hg
    simpa only [d3038, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3038, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26108 p hg
    simpa only [d3038, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26110 (p : Pattern) (guard : d5843 p = 1) : d3039 p ≤ (0 : Int) + d3766 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3039, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d3039, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3039, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26109 p hg
    simpa only [d3039, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26111 (p : Pattern) (guard : d5843 p = 1) : d1948 p ≤ (0 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1948, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d1948, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1948, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19887 p hg
    simpa only [d5843, d1948, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26112 (p : Pattern) (guard : d5843 p = 1) : d1949 p ≤ (0 : Int) + d3823 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1949, d3823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26111 p hg
    simpa only [d1949, d3823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1949, d3823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d1949, d3823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26113 (p : Pattern) (guard : d5843 p = 1) : d1950 p ≤ (0 : Int) + d3824 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1950, d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d1950, d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1950, d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26112 p hg
    simpa only [d1950, d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26114 (p : Pattern) (guard : d5843 p = 1) : d1951 p ≤ (0 : Int) + d3825 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1951, d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26043 p hg
    simpa only [d1951, d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1951, d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26113 p hg
    simpa only [d1951, d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26115 (p : Pattern) (guard : d5843 p = 1) : d1952 p ≤ (0 : Int) + d3826 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1952, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26114 p hg
    simpa only [d1952, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1952, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1952, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26116 (p : Pattern) (guard : d5843 p = 1) : d3040 p ≤ (0 : Int) + d3827 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3040, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26110 p hg
    simpa only [d3040, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3040, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26115 p hg
    simpa only [d3040, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26117 (p : Pattern) (guard : d5843 p = 1) : d3041 p ≤ (0 : Int) + d3828 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3041, d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26105 p hg
    simpa only [d3041, d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3041, d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26116 p hg
    simpa only [d3041, d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26118 (p : Pattern) (guard : d5843 p = 1) : d1958 p ≤ (0 : Int) + d3829 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1958, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26046 p hg
    simpa only [d1958, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1958, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1958, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26119 (p : Pattern) (guard : d5843 p = 1) : d3042 p ≤ (0 : Int) + d3830 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3042, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26047 p hg
    simpa only [d3042, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3042, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26118 p hg
    simpa only [d3042, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26120 (p : Pattern) (guard : d5843 p = 1) : d1967 p ≤ (0 : Int) + d3831 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1967, d3831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26069 p hg
    simpa only [d1967, d3831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1967, d3831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1967, d3831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26121 (p : Pattern) (guard : d5843 p = 1) : d3043 p ≤ (0 : Int) + d3832 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3043, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26070 p hg
    simpa only [d3043, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3043, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26120 p hg
    simpa only [d3043, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26122 (p : Pattern) (guard : d5843 p = 1) : d3044 p ≤ (0 : Int) + d3833 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3044, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26119 p hg
    simpa only [d3044, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3044, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26121 p hg
    simpa only [d3044, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26123 (p : Pattern) (guard : d5843 p = 1) : d3045 p ≤ (0 : Int) + d3834 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3045, d3834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26117 p hg
    simpa only [d3045, d3834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3045, d3834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26122 p hg
    simpa only [d3045, d3834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26124 (p : Pattern) (guard : d5843 p = 1) : d3046 p ≤ (0 : Int) + d3835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3046, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26122 p hg
    simpa only [d3046, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3046, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26038 p hg
    simpa only [d3046, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26125 (p : Pattern) (guard : d5843 p = 1) : d3047 p ≤ (0 : Int) + d3836 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3047, d3836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26123 p hg
    simpa only [d3047, d3836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3047, d3836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26124 p hg
    simpa only [d3047, d3836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26126 (p : Pattern) (guard : d5843 p = 1) : d3048 p ≤ (0 : Int) + d3837 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3048, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26091 p hg
    simpa only [d3048, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3048, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26054 p hg
    simpa only [d3048, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26127 (p : Pattern) (guard : d5843 p = 1) : d3049 p ≤ (0 : Int) + d3838 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3049, d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20210 p hg
    simpa only [d3049, d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3049, d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26059 p hg
    simpa only [d3049, d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26128 (p : Pattern) (guard : d5843 p = 1) : d3050 p ≤ (0 : Int) + d3839 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3050, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26127 p hg
    simpa only [d3050, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3050, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26060 p hg
    simpa only [d3050, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26129 (p : Pattern) (guard : d5843 p = 1) : d3051 p ≤ (0 : Int) + d3840 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3051, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26126 p hg
    simpa only [d3051, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3051, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26128 p hg
    simpa only [d3051, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26130 (p : Pattern) (guard : d5843 p = 1) : d3052 p ≤ (0 : Int) + d3841 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3052, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26129 p hg
    simpa only [d3052, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3052, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3052, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26131 (p : Pattern) (guard : d5843 p = 1) : d3053 p ≤ (0 : Int) + d3842 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3053, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26130 p hg
    simpa only [d3053, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3053, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3053, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26132 (p : Pattern) (guard : d5843 p = 1) : d3054 p ≤ (0 : Int) + d3843 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3054, d3843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26125 p hg
    simpa only [d3054, d3843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3054, d3843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26131 p hg
    simpa only [d3054, d3843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26133 (p : Pattern) (guard : d5843 p = 1) : d3055 p ≤ (0 : Int) + d3844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3055, d3844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26116 p hg
    simpa only [d3055, d3844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3055, d3844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26126 p hg
    simpa only [d3055, d3844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26134 (p : Pattern) (guard : d5843 p = 1) : d3056 p ≤ (0 : Int) + d3845 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3056, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26121 p hg
    simpa only [d3056, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3056, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25915 p hg
    simpa only [d3056, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26135 (p : Pattern) (guard : d5843 p = 1) : d3057 p ≤ (0 : Int) + d3846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3057, d3846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26133 p hg
    simpa only [d3057, d3846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3057, d3846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26134 p hg
    simpa only [d3057, d3846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26136 (p : Pattern) (guard : d5843 p = 1) : d3058 p ≤ (0 : Int) + d3847 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3058, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26121 p hg
    simpa only [d3058, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3058, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25918 p hg
    simpa only [d3058, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26137 (p : Pattern) (guard : d5843 p = 1) : d3059 p ≤ (0 : Int) + d3848 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3059, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26136 p hg
    simpa only [d3059, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3059, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3059, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26138 (p : Pattern) (guard : d5843 p = 1) : d3060 p ≤ (0 : Int) + d3849 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3060, d3849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26135 p hg
    simpa only [d3060, d3849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3060, d3849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26137 p hg
    simpa only [d3060, d3849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26139 (p : Pattern) (guard : d5843 p = 1) : d3061 p ≤ (0 : Int) + d3850 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3061, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26128 p hg
    simpa only [d3061, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3061, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3061, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26140 (p : Pattern) (guard : d5843 p = 1) : d3062 p ≤ (0 : Int) + d3851 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3062, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26139 p hg
    simpa only [d3062, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3062, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3062, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26141 (p : Pattern) (guard : d5843 p = 1) : d3063 p ≤ (0 : Int) + d3852 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3063, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26140 p hg
    simpa only [d3063, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3063, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3063, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26142 (p : Pattern) (guard : d5843 p = 1) : d3064 p ≤ (0 : Int) + d3853 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3064, d3853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26138 p hg
    simpa only [d3064, d3853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3064, d3853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26141 p hg
    simpa only [d3064, d3853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26143 (p : Pattern) (guard : d5843 p = 1) : d3065 p ≤ (0 : Int) + d3854 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3065, d3854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26132 p hg
    simpa only [d3065, d3854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3065, d3854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26142 p hg
    simpa only [d3065, d3854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26144 (p : Pattern) (guard : d5843 p = 1) : d3066 p ≤ (0 : Int) + d3855 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3066, d3855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26100 p hg
    simpa only [d3066, d3855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3066, d3855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26143 p hg
    simpa only [d3066, d3855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26145 (p : Pattern) (guard : d5843 p = 1) : d3067 p ≤ (0 : Int) + d3856 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3067, d3856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26038 p hg
    simpa only [d3067, d3856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3067, d3856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3067, d3856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26146 (p : Pattern) (guard : d5843 p = 1) : d3068 p ≤ (0 : Int) + d3857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3068, d3857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26145 p hg
    simpa only [d3068, d3857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3068, d3857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3068, d3857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26147 (p : Pattern) (guard : d5843 p = 1) : d3069 p ≤ (0 : Int) + d3858 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3069, d3858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26146 p hg
    simpa only [d3069, d3858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3069, d3858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3069, d3858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26148 (p : Pattern) (guard : d5843 p = 1) : d3070 p ≤ (0 : Int) + d3859 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3070, d3859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26147 p hg
    simpa only [d3070, d3859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3070, d3859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3070, d3859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26149 (p : Pattern) (guard : d5843 p = 1) : d3071 p ≤ (0 : Int) + d3860 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3071, d3860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26143 p hg
    simpa only [d3071, d3860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3071, d3860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26148 p hg
    simpa only [d3071, d3860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26150 (p : Pattern) (guard : d5843 p = 1) : d3072 p ≤ (0 : Int) + d3861 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3072, d3861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26144 p hg
    simpa only [d3072, d3861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3072, d3861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26149 p hg
    simpa only [d3072, d3861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26151 (p : Pattern) (guard : d5843 p = 1) : d2998 p ≤ (0 : Int) + d3862 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2998, d3862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26027 p hg
    simpa only [d2998, d3862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2998, d3862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26036 p hg
    simpa only [d2998, d3862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26152 (p : Pattern) (guard : d5843 p = 1) : d3001 p ≤ (0 : Int) + d3863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3001, d3863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26151 p hg
    simpa only [d3001, d3863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3001, d3863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26039 p hg
    simpa only [d3001, d3863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26153 (p : Pattern) (guard : d5843 p = 1) : d3014 p ≤ (0 : Int) + d3864 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3014, d3864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26152 p hg
    simpa only [d3014, d3864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3014, d3864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26076 p hg
    simpa only [d3014, d3864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26154 (p : Pattern) (guard : d5843 p = 1) : d3032 p ≤ (0 : Int) + d3865 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3032, d3865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26153 p hg
    simpa only [d3032, d3865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3032, d3865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26099 p hg
    simpa only [d3032, d3865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26155 (p : Pattern) (guard : d5843 p = 1) : d3066 p ≤ (0 : Int) + d3866 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3066, d3866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26154 p hg
    simpa only [d3066, d3866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3066, d3866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26143 p hg
    simpa only [d3066, d3866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26156 (p : Pattern) (guard : d5843 p = 1) : d3073 p ≤ (0 : Int) + d3867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3073, d3867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26143 p hg
    simpa only [d3073, d3867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3073, d3867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3073, d3867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26157 (p : Pattern) (guard : d5843 p = 1) : d3074 p ≤ (0 : Int) + d3868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3074, d3868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26155 p hg
    simpa only [d3074, d3868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3074, d3868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26156 p hg
    simpa only [d3074, d3868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26158 (p : Pattern) (guard : d5843 p = 1) : d3075 p ≤ (0 : Int) + d3869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3075, d3869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26150 p hg
    simpa only [d3075, d3869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3075, d3869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26157 p hg
    simpa only [d3075, d3869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26159 (p : Pattern) (guard : d5843 p = 1) : d3076 p ≤ (0 : Int) + d3870 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3076, d3870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26003 p hg
    simpa only [d3076, d3870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3076, d3870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26158 p hg
    simpa only [d3076, d3870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26160 (p : Pattern) (guard : d5843 p = 1) : d3077 p ≤ (0 : Int) + d3871 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3077, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26016 p hg
    simpa only [d3077, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3077, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26159 p hg
    simpa only [d3077, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26161 (p : Pattern) (guard : d5843 p = 1) : d3078 p ≤ (0 : Int) + d3872 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3078, d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20537 p hg
    simpa only [d3078, d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3078, d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25881 p hg
    simpa only [d3078, d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26162 (p : Pattern) (guard : d5843 p = 1) : d3079 p ≤ (0 : Int) + d3873 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3079, d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25882 p hg
    simpa only [d3079, d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3079, d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26161 p hg
    simpa only [d3079, d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26163 (p : Pattern) (guard : d5843 p = 1) : d3080 p ≤ (0 : Int) + d3874 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3080, d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d3080, d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3080, d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26162 p hg
    simpa only [d3080, d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26164 (p : Pattern) (guard : d5843 p = 1) : d2013 p ≤ (0 : Int) + d3875 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2013, d3875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25835 p hg
    simpa only [d2013, d3875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2013, d3875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2013, d3875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26165 (p : Pattern) (guard : d5843 p = 1) : d3081 p ≤ (0 : Int) + d3876 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3081, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26163 p hg
    simpa only [d3081, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3081, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26164 p hg
    simpa only [d3081, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26166 (p : Pattern) (guard : d5843 p = 1) : d3082 p ≤ (0 : Int) + d3877 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3082, d3877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25939 p hg
    simpa only [d3082, d3877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3082, d3877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26165 p hg
    simpa only [d3082, d3877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26167 (p : Pattern) (guard : d5843 p = 1) : d3083 p ≤ (0 : Int) + d3878 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3083, d3878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25939 p hg
    simpa only [d3083, d3878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3083, d3878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26166 p hg
    simpa only [d3083, d3878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26168 (p : Pattern) (guard : d5843 p = 1) : d3084 p ≤ (0 : Int) + d3879 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3084, d3879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26166 p hg
    simpa only [d3084, d3879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3084, d3879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25960 p hg
    simpa only [d3084, d3879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26169 (p : Pattern) (guard : d5843 p = 1) : d3085 p ≤ (0 : Int) + d3880 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3085, d3880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26167 p hg
    simpa only [d3085, d3880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3085, d3880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26168 p hg
    simpa only [d3085, d3880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26170 (p : Pattern) (guard : d5843 p = 1) : d3086 p ≤ (0 : Int) + d3881 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3086, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25922 p hg
    simpa only [d3086, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3086, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25873 p hg
    simpa only [d3086, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26171 (p : Pattern) (guard : d5843 p = 1) : d3087 p ≤ (0 : Int) + d3882 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3087, d3882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25963 p hg
    simpa only [d3087, d3882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3087, d3882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26170 p hg
    simpa only [d3087, d3882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26172 (p : Pattern) (guard : d5843 p = 1) : d3088 p ≤ (0 : Int) + d3883 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3088, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25922 p hg
    simpa only [d3088, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3088, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25878 p hg
    simpa only [d3088, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26173 (p : Pattern) (guard : d5843 p = 1) : d3089 p ≤ (0 : Int) + d3884 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3089, d3884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25964 p hg
    simpa only [d3089, d3884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3089, d3884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3089, d3884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26174 (p : Pattern) (guard : d5843 p = 1) : d3090 p ≤ (0 : Int) + d3885 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3090, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26172 p hg
    simpa only [d3090, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3090, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26173 p hg
    simpa only [d3090, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26175 (p : Pattern) (guard : d5843 p = 1) : d3091 p ≤ (0 : Int) + d3886 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3091, d3886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26171 p hg
    simpa only [d3091, d3886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3091, d3886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26174 p hg
    simpa only [d3091, d3886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26176 (p : Pattern) (guard : d5843 p = 1) : d3092 p ≤ (0 : Int) + d3887 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3092, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25923 p hg
    simpa only [d3092, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3092, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26173 p hg
    simpa only [d3092, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26177 (p : Pattern) (guard : d5843 p = 1) : d3093 p ≤ (0 : Int) + d3888 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3093, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26176 p hg
    simpa only [d3093, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3093, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25930 p hg
    simpa only [d3093, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26178 (p : Pattern) (guard : d5843 p = 1) : d3094 p ≤ (0 : Int) + d3889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3094, d3889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26175 p hg
    simpa only [d3094, d3889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3094, d3889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26177 p hg
    simpa only [d3094, d3889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26179 (p : Pattern) (guard : d5843 p = 1) : d3095 p ≤ (0 : Int) + d3890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3095, d3890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26169 p hg
    simpa only [d3095, d3890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3095, d3890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26178 p hg
    simpa only [d3095, d3890, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
