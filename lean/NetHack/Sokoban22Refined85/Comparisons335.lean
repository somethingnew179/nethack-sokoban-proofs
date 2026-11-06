/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons334
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46900 (p : Pattern) (guard : d8139 p = 1) : d2992 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46852 p hg
    simpa only [d8139, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46899 p hg
    simpa only [d8139, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46901 (p : Pattern) (guard : d8085 p = 1) : d1941 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1941, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35088 p hg
    simpa only [d8085, d1941, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1941, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42658 p hg
    simpa only [d8085, d1941, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46902 (p : Pattern) (guard : d8089 p = 1) : d1940 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42658 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46903 (p : Pattern) (guard : d8090 p = 1) : d1942 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1942, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46901 p hg
    simpa only [d8090, d1942, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1942, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46902 p hg
    simpa only [d8090, d1942, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46904 (p : Pattern) (guard : d8091 p = 1) : d2993 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2993, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35096 p hg
    simpa only [d8091, d2993, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2993, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46903 p hg
    simpa only [d8091, d2993, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46905 (p : Pattern) (guard : d8096 p = 1) : d2994 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2994, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46904 p hg
    simpa only [d8096, d2994, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2994, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39143 p hg
    simpa only [d8096, d2994, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46906 (p : Pattern) (guard : d8095 p = 1) : d2993 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2993, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35113 p hg
    simpa only [d8095, d2993, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2993, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39237 p hg
    simpa only [d8095, d2993, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46907 (p : Pattern) (guard : d8101 p = 1) : d2994 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2994, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46906 p hg
    simpa only [d8101, d2994, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2994, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39149 p hg
    simpa only [d8101, d2994, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46908 (p : Pattern) (guard : d8102 p = 1) : d2994 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46905 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46907 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46909 (p : Pattern) (guard : d8095 p = 1) : d2993 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2993, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35124 p hg
    simpa only [d8095, d2993, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2993, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39237 p hg
    simpa only [d8095, d2993, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46910 (p : Pattern) (guard : d8101 p = 1) : d2994 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2994, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46909 p hg
    simpa only [d8101, d2994, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2994, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39155 p hg
    simpa only [d8101, d2994, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46911 (p : Pattern) (guard : d5854 p = 1) : d2129 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d5854, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17585 p hg
    simpa only [d5854, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46912 (p : Pattern) (guard : d8099 p = 1) : d2130 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46911 p hg
    simpa only [d8099, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17585 p hg
    simpa only [d8099, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46913 (p : Pattern) (guard : d8100 p = 1) : d2995 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2995, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35136 p hg
    simpa only [d8100, d2995, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2995, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46912 p hg
    simpa only [d8100, d2995, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46914 (p : Pattern) (guard : d8106 p = 1) : d2996 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2996, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46913 p hg
    simpa only [d8106, d2996, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2996, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39160 p hg
    simpa only [d8106, d2996, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46915 (p : Pattern) (guard : d8107 p = 1) : d2997 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2997, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46910 p hg
    simpa only [d8107, d2997, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2997, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46914 p hg
    simpa only [d8107, d2997, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46916 (p : Pattern) (guard : d8108 p = 1) : d2998 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2998, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46908 p hg
    simpa only [d8108, d2998, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2998, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46915 p hg
    simpa only [d8108, d2998, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46917 (p : Pattern) (guard : d8095 p = 1) : d2993 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2993, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35147 p hg
    simpa only [d8095, d2993, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2993, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39237 p hg
    simpa only [d8095, d2993, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46918 (p : Pattern) (guard : d8101 p = 1) : d2994 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2994, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46917 p hg
    simpa only [d8101, d2994, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2994, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39155 p hg
    simpa only [d8101, d2994, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46919 (p : Pattern) (guard : d8100 p = 1) : d2995 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2995, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35153 p hg
    simpa only [d8100, d2995, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2995, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46912 p hg
    simpa only [d8100, d2995, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46920 (p : Pattern) (guard : d8106 p = 1) : d2996 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2996, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46919 p hg
    simpa only [d8106, d2996, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2996, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39160 p hg
    simpa only [d8106, d2996, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46921 (p : Pattern) (guard : d8107 p = 1) : d2997 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2997, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46918 p hg
    simpa only [d8107, d2997, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2997, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46920 p hg
    simpa only [d8107, d2997, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46922 (p : Pattern) (guard : d8112 p = 1) : d2999 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2999, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46800 p hg
    simpa only [d8112, d2999, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2999, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2999, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46923 (p : Pattern) (guard : d8113 p = 1) : d3000 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3000, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46921 p hg
    simpa only [d8113, d3000, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3000, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46922 p hg
    simpa only [d8113, d3000, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46924 (p : Pattern) (guard : d8114 p = 1) : d3001 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3001, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46916 p hg
    simpa only [d8114, d3001, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3001, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46923 p hg
    simpa only [d8114, d3001, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46925 (p : Pattern) (guard : d5843 p = 1) : d1945 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d5843, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20207 p hg
    simpa only [d5843, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46926 (p : Pattern) (guard : d5847 p = 1) : d1946 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46925 p hg
    simpa only [d5847, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46927 (p : Pattern) (guard : d8089 p = 1) : d1947 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8089, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46926 p hg
    simpa only [d8089, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46928 (p : Pattern) (guard : d5854 p = 1) : d1956 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d5854, d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17401 p hg
    simpa only [d5854, d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46929 (p : Pattern) (guard : d8094 p = 1) : d1957 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46927 p hg
    simpa only [d8094, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46928 p hg
    simpa only [d8094, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46930 (p : Pattern) (guard : d8095 p = 1) : d3002 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3002, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35163 p hg
    simpa only [d8095, d3002, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3002, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46929 p hg
    simpa only [d8095, d3002, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46931 (p : Pattern) (guard : d8101 p = 1) : d3003 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3003, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46930 p hg
    simpa only [d8101, d3003, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3003, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39180 p hg
    simpa only [d8101, d3003, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46932 (p : Pattern) (guard : d8100 p = 1) : d3002 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3002, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35177 p hg
    simpa only [d8100, d3002, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3002, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39247 p hg
    simpa only [d8100, d3002, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46933 (p : Pattern) (guard : d8106 p = 1) : d3004 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3004, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46932 p hg
    simpa only [d8106, d3004, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3004, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39185 p hg
    simpa only [d8106, d3004, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46934 (p : Pattern) (guard : d8107 p = 1) : d3005 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3005, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46931 p hg
    simpa only [d8107, d3005, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3005, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46933 p hg
    simpa only [d8107, d3005, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46935 (p : Pattern) (guard : d8100 p = 1) : d3002 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3002, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35117 p hg
    simpa only [d8100, d3002, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3002, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39247 p hg
    simpa only [d8100, d3002, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46936 (p : Pattern) (guard : d8106 p = 1) : d3006 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3006, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46935 p hg
    simpa only [d8106, d3006, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3006, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3006, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46937 (p : Pattern) (guard : d8105 p = 1) : d3007 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d8105, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24043 p hg
    simpa only [d8105, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46938 (p : Pattern) (guard : d8111 p = 1) : d3008 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46937 p hg
    simpa only [d8111, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46939 (p : Pattern) (guard : d8112 p = 1) : d3009 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3009, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46936 p hg
    simpa only [d8112, d3009, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3009, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46938 p hg
    simpa only [d8112, d3009, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46940 (p : Pattern) (guard : d8113 p = 1) : d3010 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3010, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46934 p hg
    simpa only [d8113, d3010, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3010, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46939 p hg
    simpa only [d8113, d3010, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46941 (p : Pattern) (guard : d8100 p = 1) : d3002 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35115 p hg
    simpa only [d8100, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39247 p hg
    simpa only [d8100, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46942 (p : Pattern) (guard : d8106 p = 1) : d3006 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46941 p hg
    simpa only [d8106, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46943 (p : Pattern) (guard : d8112 p = 1) : d3009 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46942 p hg
    simpa only [d8112, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46938 p hg
    simpa only [d8112, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46944 (p : Pattern) (guard : d8117 p = 1) : d3011 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46472 p hg
    simpa only [d8117, d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46945 (p : Pattern) (guard : d8118 p = 1) : d3012 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46943 p hg
    simpa only [d8118, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46944 p hg
    simpa only [d8118, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46946 (p : Pattern) (guard : d8119 p = 1) : d3013 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3013, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46940 p hg
    simpa only [d8119, d3013, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3013, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46945 p hg
    simpa only [d8119, d3013, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46947 (p : Pattern) (guard : d8120 p = 1) : d3014 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3014, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46924 p hg
    simpa only [d8120, d3014, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3014, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46946 p hg
    simpa only [d8120, d3014, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46948 (p : Pattern) (guard : d8089 p = 1) : d1941 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1941, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35111 p hg
    simpa only [d8089, d1941, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1941, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d8089, d1941, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46949 (p : Pattern) (guard : d8094 p = 1) : d1942 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1942, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46948 p hg
    simpa only [d8094, d1942, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1942, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39236 p hg
    simpa only [d8094, d1942, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46950 (p : Pattern) (guard : d8095 p = 1) : d2993 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2993, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35203 p hg
    simpa only [d8095, d2993, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2993, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46949 p hg
    simpa only [d8095, d2993, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46951 (p : Pattern) (guard : d8101 p = 1) : d2994 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2994, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46950 p hg
    simpa only [d8101, d2994, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2994, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39202 p hg
    simpa only [d8101, d2994, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46952 (p : Pattern) (guard : d5854 p = 1) : d2124 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d5854, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17578 p hg
    simpa only [d5854, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46953 (p : Pattern) (guard : d8099 p = 1) : d2125 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46952 p hg
    simpa only [d8099, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17578 p hg
    simpa only [d8099, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46954 (p : Pattern) (guard : d8100 p = 1) : d3015 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3015, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35211 p hg
    simpa only [d8100, d3015, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3015, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46953 p hg
    simpa only [d8100, d3015, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46955 (p : Pattern) (guard : d8106 p = 1) : d3016 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3016, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46954 p hg
    simpa only [d8106, d3016, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3016, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39207 p hg
    simpa only [d8106, d3016, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46956 (p : Pattern) (guard : d8107 p = 1) : d3017 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3017, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46951 p hg
    simpa only [d8107, d3017, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3017, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46955 p hg
    simpa only [d8107, d3017, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46957 (p : Pattern) (guard : d8100 p = 1) : d2995 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2995, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35220 p hg
    simpa only [d8100, d2995, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2995, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46912 p hg
    simpa only [d8100, d2995, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46958 (p : Pattern) (guard : d8106 p = 1) : d2996 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2996, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46957 p hg
    simpa only [d8106, d2996, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2996, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39160 p hg
    simpa only [d8106, d2996, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46959 (p : Pattern) (guard : d8105 p = 1) : d2927 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35224 p hg
    simpa only [d8105, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23918 p hg
    simpa only [d8105, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46960 (p : Pattern) (guard : d8111 p = 1) : d2928 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46959 p hg
    simpa only [d8111, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15307 p hg
    simpa only [d8111, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46961 (p : Pattern) (guard : d8112 p = 1) : d3018 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3018, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46958 p hg
    simpa only [d8112, d3018, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3018, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46960 p hg
    simpa only [d8112, d3018, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46962 (p : Pattern) (guard : d8113 p = 1) : d3019 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3019, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46956 p hg
    simpa only [d8113, d3019, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3019, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46961 p hg
    simpa only [d8113, d3019, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46963 (p : Pattern) (guard : d8105 p = 1) : d2930 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35230 p hg
    simpa only [d8105, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23922 p hg
    simpa only [d8105, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46964 (p : Pattern) (guard : d8111 p = 1) : d2931 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46963 p hg
    simpa only [d8111, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d8111, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46965 (p : Pattern) (guard : d8112 p = 1) : d3020 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3020, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46914 p hg
    simpa only [d8112, d3020, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3020, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46964 p hg
    simpa only [d8112, d3020, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46966 (p : Pattern) (guard : d8118 p = 1) : d3021 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3021, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46965 p hg
    simpa only [d8118, d3021, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3021, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3021, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46967 (p : Pattern) (guard : d8119 p = 1) : d3022 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3022, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46962 p hg
    simpa only [d8119, d3022, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3022, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46966 p hg
    simpa only [d8119, d3022, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46968 (p : Pattern) (guard : d8100 p = 1) : d3002 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3002, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35238 p hg
    simpa only [d8100, d3002, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3002, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39247 p hg
    simpa only [d8100, d3002, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46969 (p : Pattern) (guard : d8106 p = 1) : d3004 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3004, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46968 p hg
    simpa only [d8106, d3004, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3004, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39185 p hg
    simpa only [d8106, d3004, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46970 (p : Pattern) (guard : d8105 p = 1) : d3023 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8105, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24064 p hg
    simpa only [d8105, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46971 (p : Pattern) (guard : d8111 p = 1) : d3024 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46970 p hg
    simpa only [d8111, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46972 (p : Pattern) (guard : d8112 p = 1) : d3025 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3025, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46969 p hg
    simpa only [d8112, d3025, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3025, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46971 p hg
    simpa only [d8112, d3025, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46973 (p : Pattern) (guard : d8117 p = 1) : d3026 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46938 p hg
    simpa only [d8117, d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46702 p hg
    simpa only [d8117, d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46974 (p : Pattern) (guard : d8118 p = 1) : d3027 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3027, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46972 p hg
    simpa only [d8118, d3027, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3027, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46973 p hg
    simpa only [d8118, d3027, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46975 (p : Pattern) (guard : d0 p = 1) : d2942 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46976 (p : Pattern) (guard : d8117 p = 1) : d3028 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46938 p hg
    simpa only [d8117, d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46975 p hg
    simpa only [d8117, d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46977 (p : Pattern) (guard : d8123 p = 1) : d3029 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46976 p hg
    simpa only [d8123, d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46978 (p : Pattern) (guard : d8124 p = 1) : d3030 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3030, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46974 p hg
    simpa only [d8124, d3030, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3030, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46977 p hg
    simpa only [d8124, d3030, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46979 (p : Pattern) (guard : d8125 p = 1) : d3031 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3031, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46967 p hg
    simpa only [d8125, d3031, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3031, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46978 p hg
    simpa only [d8125, d3031, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46980 (p : Pattern) (guard : d8126 p = 1) : d3032 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3032, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46947 p hg
    simpa only [d8126, d3032, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3032, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46979 p hg
    simpa only [d8126, d3032, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46981 (p : Pattern) (guard : d5854 p = 1) : d2107 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d5854, d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17393 p hg
    simpa only [d5854, d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46982 (p : Pattern) (guard : d8094 p = 1) : d2108 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46927 p hg
    simpa only [d8094, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46981 p hg
    simpa only [d8094, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46983 (p : Pattern) (guard : d8095 p = 1) : d3033 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3033, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35147 p hg
    simpa only [d8095, d3033, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3033, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46982 p hg
    simpa only [d8095, d3033, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46984 (p : Pattern) (guard : d8101 p = 1) : d3034 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3034, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46983 p hg
    simpa only [d8101, d3034, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3034, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39238 p hg
    simpa only [d8101, d3034, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46985 (p : Pattern) (guard : d0 p = 1) : d3037 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46986 (p : Pattern) (guard : d8099 p = 1) : d3038 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39240 p hg
    simpa only [d8099, d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46985 p hg
    simpa only [d8099, d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46987 (p : Pattern) (guard : d8100 p = 1) : d3039 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3039, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35238 p hg
    simpa only [d8100, d3039, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3039, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46986 p hg
    simpa only [d8100, d3039, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46988 (p : Pattern) (guard : d8106 p = 1) : d3040 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3040, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46987 p hg
    simpa only [d8106, d3040, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3040, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39243 p hg
    simpa only [d8106, d3040, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46989 (p : Pattern) (guard : d8107 p = 1) : d3041 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3041, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46984 p hg
    simpa only [d8107, d3041, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3041, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46988 p hg
    simpa only [d8107, d3041, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46990 (p : Pattern) (guard : d8106 p = 1) : d3042 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3042, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46932 p hg
    simpa only [d8106, d3042, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3042, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39248 p hg
    simpa only [d8106, d3042, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46991 (p : Pattern) (guard : d8111 p = 1) : d3043 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46937 p hg
    simpa only [d8111, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15472 p hg
    simpa only [d8111, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46992 (p : Pattern) (guard : d8112 p = 1) : d3044 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3044, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46990 p hg
    simpa only [d8112, d3044, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3044, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46991 p hg
    simpa only [d8112, d3044, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46993 (p : Pattern) (guard : d8113 p = 1) : d3045 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3045, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46989 p hg
    simpa only [d8113, d3045, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3045, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46992 p hg
    simpa only [d8113, d3045, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46994 (p : Pattern) (guard : d8106 p = 1) : d3042 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3042, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46935 p hg
    simpa only [d8106, d3042, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3042, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39248 p hg
    simpa only [d8106, d3042, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46995 (p : Pattern) (guard : d8112 p = 1) : d3044 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3044, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46994 p hg
    simpa only [d8112, d3044, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3044, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46991 p hg
    simpa only [d8112, d3044, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46996 (p : Pattern) (guard : d8117 p = 1) : d2999 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46512 p hg
    simpa only [d8117, d2999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46997 (p : Pattern) (guard : d8118 p = 1) : d3046 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3046, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46995 p hg
    simpa only [d8118, d3046, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3046, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46996 p hg
    simpa only [d8118, d3046, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46998 (p : Pattern) (guard : d8119 p = 1) : d3047 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3047, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46993 p hg
    simpa only [d8119, d3047, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3047, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46997 p hg
    simpa only [d8119, d3047, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46999 (p : Pattern) (guard : d8100 p = 1) : d3023 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35171 p hg
    simpa only [d8100, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39260 p hg
    simpa only [d8100, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47000 (p : Pattern) (guard : d8106 p = 1) : d3048 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46999 p hg
    simpa only [d8106, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d8106, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47001 (p : Pattern) (guard : d8105 p = 1) : d3049 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35183 p hg
    simpa only [d8105, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24089 p hg
    simpa only [d8105, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47002 (p : Pattern) (guard : d8111 p = 1) : d3050 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47001 p hg
    simpa only [d8111, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d8111, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47003 (p : Pattern) (guard : d8112 p = 1) : d3051 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47000 p hg
    simpa only [d8112, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47002 p hg
    simpa only [d8112, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47004 (p : Pattern) (guard : d8118 p = 1) : d3052 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47003 p hg
    simpa only [d8118, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47005 (p : Pattern) (guard : d8124 p = 1) : d3053 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47004 p hg
    simpa only [d8124, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47006 (p : Pattern) (guard : d8125 p = 1) : d3054 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3054, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46998 p hg
    simpa only [d8125, d3054, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3054, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47005 p hg
    simpa only [d8125, d3054, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47007 (p : Pattern) (guard : d8100 p = 1) : d3039 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3039, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35274 p hg
    simpa only [d8100, d3039, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3039, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46986 p hg
    simpa only [d8100, d3039, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47008 (p : Pattern) (guard : d8106 p = 1) : d3040 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3040, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47007 p hg
    simpa only [d8106, d3040, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3040, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39243 p hg
    simpa only [d8106, d3040, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47009 (p : Pattern) (guard : d8105 p = 1) : d3023 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3023, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35281 p hg
    simpa only [d8105, d3023, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3023, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24064 p hg
    simpa only [d8105, d3023, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47010 (p : Pattern) (guard : d8111 p = 1) : d3048 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3048, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47009 p hg
    simpa only [d8111, d3048, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3048, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d8111, d3048, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47011 (p : Pattern) (guard : d8112 p = 1) : d3055 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3055, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47008 p hg
    simpa only [d8112, d3055, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3055, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47010 p hg
    simpa only [d8112, d3055, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47012 (p : Pattern) (guard : d8117 p = 1) : d3056 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46991 p hg
    simpa only [d8117, d3056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d8117, d3056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47013 (p : Pattern) (guard : d8118 p = 1) : d3057 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3057, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47011 p hg
    simpa only [d8118, d3057, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3057, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47012 p hg
    simpa only [d8118, d3057, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47014 (p : Pattern) (guard : d0 p = 1) : d2931 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47015 (p : Pattern) (guard : d8117 p = 1) : d3058 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46991 p hg
    simpa only [d8117, d3058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47014 p hg
    simpa only [d8117, d3058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47016 (p : Pattern) (guard : d8123 p = 1) : d3059 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47015 p hg
    simpa only [d8123, d3059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47017 (p : Pattern) (guard : d8124 p = 1) : d3060 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3060, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47013 p hg
    simpa only [d8124, d3060, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3060, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47016 p hg
    simpa only [d8124, d3060, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47018 (p : Pattern) (guard : d8117 p = 1) : d3061 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47002 p hg
    simpa only [d8117, d3061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47019 (p : Pattern) (guard : d8123 p = 1) : d3062 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47018 p hg
    simpa only [d8123, d3062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47020 (p : Pattern) (guard : d8129 p = 1) : d3063 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47019 p hg
    simpa only [d8129, d3063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47021 (p : Pattern) (guard : d8130 p = 1) : d3064 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3064, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47017 p hg
    simpa only [d8130, d3064, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3064, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47020 p hg
    simpa only [d8130, d3064, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47022 (p : Pattern) (guard : d8131 p = 1) : d3065 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3065, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47006 p hg
    simpa only [d8131, d3065, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3065, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47021 p hg
    simpa only [d8131, d3065, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47023 (p : Pattern) (guard : d8132 p = 1) : d3066 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3066, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46980 p hg
    simpa only [d8132, d3066, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3066, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47022 p hg
    simpa only [d8132, d3066, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47024 (p : Pattern) (guard : d8095 p = 1) : d3033 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3033, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35124 p hg
    simpa only [d8095, d3033, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3033, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46982 p hg
    simpa only [d8095, d3033, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47025 (p : Pattern) (guard : d8101 p = 1) : d3034 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3034, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47024 p hg
    simpa only [d8101, d3034, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3034, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39238 p hg
    simpa only [d8101, d3034, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47026 (p : Pattern) (guard : d8107 p = 1) : d3041 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3041, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47025 p hg
    simpa only [d8107, d3041, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3041, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47008 p hg
    simpa only [d8107, d3041, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47027 (p : Pattern) (guard : d8106 p = 1) : d3042 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3042, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46968 p hg
    simpa only [d8106, d3042, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3042, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39248 p hg
    simpa only [d8106, d3042, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47028 (p : Pattern) (guard : d8112 p = 1) : d3044 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3044, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47027 p hg
    simpa only [d8112, d3044, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3044, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46991 p hg
    simpa only [d8112, d3044, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47029 (p : Pattern) (guard : d8113 p = 1) : d3045 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3045, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47026 p hg
    simpa only [d8113, d3045, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3045, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47028 p hg
    simpa only [d8113, d3045, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47030 (p : Pattern) (guard : d8118 p = 1) : d3046 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3046, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46992 p hg
    simpa only [d8118, d3046, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3046, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46996 p hg
    simpa only [d8118, d3046, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47031 (p : Pattern) (guard : d8119 p = 1) : d3047 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3047, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47029 p hg
    simpa only [d8119, d3047, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3047, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47030 p hg
    simpa only [d8119, d3047, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47032 (p : Pattern) (guard : d8100 p = 1) : d3023 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3023, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38208 p hg
    simpa only [d8100, d3023, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3023, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39260 p hg
    simpa only [d8100, d3023, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47033 (p : Pattern) (guard : d8106 p = 1) : d3048 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3048, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47032 p hg
    simpa only [d8106, d3048, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3048, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d8106, d3048, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47034 (p : Pattern) (guard : d8112 p = 1) : d3051 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3051, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47033 p hg
    simpa only [d8112, d3051, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3051, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47002 p hg
    simpa only [d8112, d3051, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47035 (p : Pattern) (guard : d8118 p = 1) : d3052 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3052, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47034 p hg
    simpa only [d8118, d3052, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3052, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3052, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47036 (p : Pattern) (guard : d8124 p = 1) : d3053 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3053, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47035 p hg
    simpa only [d8124, d3053, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3053, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3053, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47037 (p : Pattern) (guard : d8125 p = 1) : d3054 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3054, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47031 p hg
    simpa only [d8125, d3054, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3054, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47036 p hg
    simpa only [d8125, d3054, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47038 (p : Pattern) (guard : d8100 p = 1) : d3039 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3039, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35300 p hg
    simpa only [d8100, d3039, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3039, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46986 p hg
    simpa only [d8100, d3039, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47039 (p : Pattern) (guard : d8106 p = 1) : d3040 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3040, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47038 p hg
    simpa only [d8106, d3040, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3040, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39243 p hg
    simpa only [d8106, d3040, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
