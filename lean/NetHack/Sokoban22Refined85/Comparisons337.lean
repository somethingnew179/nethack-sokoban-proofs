/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons336
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47180 (p : Pattern) (guard : d8101 p = 1) : d2896 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47179 p hg
    simpa only [d8101, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39439 p hg
    simpa only [d8101, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47181 (p : Pattern) (guard : d8100 p = 1) : d2922 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2922, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35418 p hg
    simpa only [d8100, d2922, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2922, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46684 p hg
    simpa only [d8100, d2922, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47182 (p : Pattern) (guard : d8106 p = 1) : d2923 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2923, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47181 p hg
    simpa only [d8106, d2923, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2923, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d8106, d2923, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47183 (p : Pattern) (guard : d8107 p = 1) : d2924 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2924, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47180 p hg
    simpa only [d8107, d2924, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2924, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47182 p hg
    simpa only [d8107, d2924, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47184 (p : Pattern) (guard : d8100 p = 1) : d2897 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35424 p hg
    simpa only [d8100, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d8100, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47185 (p : Pattern) (guard : d8106 p = 1) : d2898 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47184 p hg
    simpa only [d8106, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47186 (p : Pattern) (guard : d8105 p = 1) : d2901 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35430 p hg
    simpa only [d8105, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23885 p hg
    simpa only [d8105, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47187 (p : Pattern) (guard : d8111 p = 1) : d2902 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47186 p hg
    simpa only [d8111, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15276 p hg
    simpa only [d8111, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47188 (p : Pattern) (guard : d8112 p = 1) : d2925 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2925, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47185 p hg
    simpa only [d8112, d2925, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2925, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47187 p hg
    simpa only [d8112, d2925, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47189 (p : Pattern) (guard : d8113 p = 1) : d2926 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2926, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47183 p hg
    simpa only [d8113, d2926, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2926, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47188 p hg
    simpa only [d8113, d2926, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47190 (p : Pattern) (guard : d8105 p = 1) : d2927 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2927, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35438 p hg
    simpa only [d8105, d2927, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2927, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23918 p hg
    simpa only [d8105, d2927, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47191 (p : Pattern) (guard : d8111 p = 1) : d2928 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2928, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47190 p hg
    simpa only [d8111, d2928, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2928, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15307 p hg
    simpa only [d8111, d2928, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47192 (p : Pattern) (guard : d8112 p = 1) : d2929 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2929, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47162 p hg
    simpa only [d8112, d2929, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2929, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47191 p hg
    simpa only [d8112, d2929, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47193 (p : Pattern) (guard : d8118 p = 1) : d2933 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2933, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47192 p hg
    simpa only [d8118, d2933, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2933, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2933, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47194 (p : Pattern) (guard : d8119 p = 1) : d2934 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2934, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47189 p hg
    simpa only [d8119, d2934, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2934, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47193 p hg
    simpa only [d8119, d2934, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47195 (p : Pattern) (guard : d8100 p = 1) : d2906 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35446 p hg
    simpa only [d8100, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38955 p hg
    simpa only [d8100, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47196 (p : Pattern) (guard : d8106 p = 1) : d2908 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47195 p hg
    simpa only [d8106, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47197 (p : Pattern) (guard : d8112 p = 1) : d2937 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2937, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47196 p hg
    simpa only [d8112, d2937, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2937, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46697 p hg
    simpa only [d8112, d2937, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47198 (p : Pattern) (guard : d8118 p = 1) : d2939 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2939, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47197 p hg
    simpa only [d8118, d2939, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2939, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46700 p hg
    simpa only [d8118, d2939, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47199 (p : Pattern) (guard : d8124 p = 1) : d2945 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2945, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47198 p hg
    simpa only [d8124, d2945, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2945, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d8124, d2945, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47200 (p : Pattern) (guard : d8125 p = 1) : d2946 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2946, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47194 p hg
    simpa only [d8125, d2946, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2946, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47199 p hg
    simpa only [d8125, d2946, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47201 (p : Pattern) (guard : d8126 p = 1) : d2947 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2947, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47178 p hg
    simpa only [d8126, d2947, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2947, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47200 p hg
    simpa only [d8126, d2947, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47202 (p : Pattern) (guard : d8095 p = 1) : d2948 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d8095, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d8095, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47203 (p : Pattern) (guard : d8101 p = 1) : d2949 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47202 p hg
    simpa only [d8101, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47204 (p : Pattern) (guard : d8107 p = 1) : d2952 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2952, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47203 p hg
    simpa only [d8107, d2952, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2952, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46892 p hg
    simpa only [d8107, d2952, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47205 (p : Pattern) (guard : d8106 p = 1) : d2953 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47171 p hg
    simpa only [d8106, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47206 (p : Pattern) (guard : d8112 p = 1) : d2955 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47205 p hg
    simpa only [d8112, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d8112, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47207 (p : Pattern) (guard : d8113 p = 1) : d2956 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2956, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47204 p hg
    simpa only [d8113, d2956, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2956, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47206 p hg
    simpa only [d8113, d2956, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47208 (p : Pattern) (guard : d8118 p = 1) : d2959 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2959, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46887 p hg
    simpa only [d8118, d2959, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2959, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46722 p hg
    simpa only [d8118, d2959, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47209 (p : Pattern) (guard : d8119 p = 1) : d2960 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2960, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47207 p hg
    simpa only [d8119, d2960, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2960, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47208 p hg
    simpa only [d8119, d2960, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47210 (p : Pattern) (guard : d8125 p = 1) : d2967 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2967, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47209 p hg
    simpa only [d8125, d2967, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2967, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d8125, d2967, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47211 (p : Pattern) (guard : d8100 p = 1) : d2950 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35464 p hg
    simpa only [d8100, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d8100, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47212 (p : Pattern) (guard : d8106 p = 1) : d2951 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47211 p hg
    simpa only [d8106, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47213 (p : Pattern) (guard : d8105 p = 1) : d2935 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35470 p hg
    simpa only [d8105, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23928 p hg
    simpa only [d8105, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47214 (p : Pattern) (guard : d8111 p = 1) : d2961 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47213 p hg
    simpa only [d8111, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d8111, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47215 (p : Pattern) (guard : d8112 p = 1) : d2968 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2968, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47212 p hg
    simpa only [d8112, d2968, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2968, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47214 p hg
    simpa only [d8112, d2968, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47216 (p : Pattern) (guard : d8118 p = 1) : d2970 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2970, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47215 p hg
    simpa only [d8118, d2970, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2970, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46736 p hg
    simpa only [d8118, d2970, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47217 (p : Pattern) (guard : d8124 p = 1) : d2973 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2973, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47216 p hg
    simpa only [d8124, d2973, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2973, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d8124, d2973, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47218 (p : Pattern) (guard : d8130 p = 1) : d2977 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2977, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47217 p hg
    simpa only [d8130, d2977, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2977, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46745 p hg
    simpa only [d8130, d2977, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47219 (p : Pattern) (guard : d8131 p = 1) : d2978 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2978, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47210 p hg
    simpa only [d8131, d2978, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2978, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47218 p hg
    simpa only [d8131, d2978, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47220 (p : Pattern) (guard : d8132 p = 1) : d2979 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2979, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47201 p hg
    simpa only [d8132, d2979, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2979, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47219 p hg
    simpa only [d8132, d2979, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47221 (p : Pattern) (guard : d8095 p = 1) : d2948 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d8095, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d8095, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47222 (p : Pattern) (guard : d8101 p = 1) : d2949 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47221 p hg
    simpa only [d8101, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47223 (p : Pattern) (guard : d8107 p = 1) : d2952 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47222 p hg
    simpa only [d8107, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47212 p hg
    simpa only [d8107, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47224 (p : Pattern) (guard : d8106 p = 1) : d2953 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47195 p hg
    simpa only [d8106, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47225 (p : Pattern) (guard : d8112 p = 1) : d2955 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47224 p hg
    simpa only [d8112, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d8112, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47226 (p : Pattern) (guard : d8113 p = 1) : d2956 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47223 p hg
    simpa only [d8113, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47225 p hg
    simpa only [d8113, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47227 (p : Pattern) (guard : d8118 p = 1) : d2959 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47206 p hg
    simpa only [d8118, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46722 p hg
    simpa only [d8118, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47228 (p : Pattern) (guard : d8119 p = 1) : d2960 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47226 p hg
    simpa only [d8119, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47227 p hg
    simpa only [d8119, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47229 (p : Pattern) (guard : d8112 p = 1) : d2964 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46604 p hg
    simpa only [d8112, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46726 p hg
    simpa only [d8112, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47230 (p : Pattern) (guard : d8118 p = 1) : d2965 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47229 p hg
    simpa only [d8118, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47231 (p : Pattern) (guard : d8124 p = 1) : d2966 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47230 p hg
    simpa only [d8124, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47232 (p : Pattern) (guard : d8125 p = 1) : d2967 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47228 p hg
    simpa only [d8125, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47231 p hg
    simpa only [d8125, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47233 (p : Pattern) (guard : d8100 p = 1) : d2950 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35482 p hg
    simpa only [d8100, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d8100, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47234 (p : Pattern) (guard : d8106 p = 1) : d2951 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47233 p hg
    simpa only [d8106, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47235 (p : Pattern) (guard : d8105 p = 1) : d2935 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35627 p hg
    simpa only [d8105, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23928 p hg
    simpa only [d8105, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47236 (p : Pattern) (guard : d8111 p = 1) : d2961 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47235 p hg
    simpa only [d8111, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d8111, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47237 (p : Pattern) (guard : d8112 p = 1) : d2968 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47234 p hg
    simpa only [d8112, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47236 p hg
    simpa only [d8112, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47238 (p : Pattern) (guard : d8105 p = 1) : d2911 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35489 p hg
    simpa only [d8105, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23897 p hg
    simpa only [d8105, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47239 (p : Pattern) (guard : d8111 p = 1) : d2954 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47238 p hg
    simpa only [d8111, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15333 p hg
    simpa only [d8111, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47240 (p : Pattern) (guard : d8117 p = 1) : d2969 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47239 p hg
    simpa only [d8117, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46735 p hg
    simpa only [d8117, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47241 (p : Pattern) (guard : d8118 p = 1) : d2970 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47237 p hg
    simpa only [d8118, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47240 p hg
    simpa only [d8118, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47242 (p : Pattern) (guard : d8124 p = 1) : d2973 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47241 p hg
    simpa only [d8124, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d8124, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47243 (p : Pattern) (guard : d8130 p = 1) : d2977 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47242 p hg
    simpa only [d8130, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46745 p hg
    simpa only [d8130, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47244 (p : Pattern) (guard : d8131 p = 1) : d2978 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47232 p hg
    simpa only [d8131, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47243 p hg
    simpa only [d8131, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47245 (p : Pattern) (guard : d8106 p = 1) : d2957 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2957, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46576 p hg
    simpa only [d8106, d2957, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2957, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38558 p hg
    simpa only [d8106, d2957, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47246 (p : Pattern) (guard : d8112 p = 1) : d2980 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2980, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47245 p hg
    simpa only [d8112, d2980, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2980, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46514 p hg
    simpa only [d8112, d2980, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47247 (p : Pattern) (guard : d8118 p = 1) : d2981 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2981, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47246 p hg
    simpa only [d8118, d2981, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2981, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2981, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47248 (p : Pattern) (guard : d8123 p = 1) : d2982 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8123, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47249 (p : Pattern) (guard : d8124 p = 1) : d2983 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2983, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47247 p hg
    simpa only [d8124, d2983, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2983, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47248 p hg
    simpa only [d8124, d2983, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47250 (p : Pattern) (guard : d8129 p = 1) : d2984 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47248 p hg
    simpa only [d8129, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47251 (p : Pattern) (guard : d8130 p = 1) : d2985 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2985, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47249 p hg
    simpa only [d8130, d2985, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2985, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47250 p hg
    simpa only [d8130, d2985, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47252 (p : Pattern) (guard : d8135 p = 1) : d2986 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47250 p hg
    simpa only [d8135, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47253 (p : Pattern) (guard : d8136 p = 1) : d2987 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2987, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47251 p hg
    simpa only [d8136, d2987, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2987, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47252 p hg
    simpa only [d8136, d2987, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47254 (p : Pattern) (guard : d8137 p = 1) : d2988 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2988, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47244 p hg
    simpa only [d8137, d2988, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2988, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47253 p hg
    simpa only [d8137, d2988, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47255 (p : Pattern) (guard : d8138 p = 1) : d2989 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2989, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47220 p hg
    simpa only [d8138, d2989, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2989, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47254 p hg
    simpa only [d8138, d2989, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47256 (p : Pattern) (guard : d8095 p = 1) : d2948 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35387 p hg
    simpa only [d8095, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d8095, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47257 (p : Pattern) (guard : d8101 p = 1) : d2949 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47256 p hg
    simpa only [d8101, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39515 p hg
    simpa only [d8101, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47258 (p : Pattern) (guard : d8100 p = 1) : d2948 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35482 p hg
    simpa only [d8100, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39562 p hg
    simpa only [d8100, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47259 (p : Pattern) (guard : d8106 p = 1) : d2949 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47258 p hg
    simpa only [d8106, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d8106, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47260 (p : Pattern) (guard : d8107 p = 1) : d2949 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47257 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47259 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47261 (p : Pattern) (guard : d8100 p = 1) : d2948 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35464 p hg
    simpa only [d8100, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39562 p hg
    simpa only [d8100, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47262 (p : Pattern) (guard : d8106 p = 1) : d2949 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47261 p hg
    simpa only [d8106, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d8106, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47263 (p : Pattern) (guard : d8105 p = 1) : d3080 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3080, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35489 p hg
    simpa only [d8105, d3080, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3080, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d8105, d3080, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47264 (p : Pattern) (guard : d8111 p = 1) : d3081 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3081, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47263 p hg
    simpa only [d8111, d3081, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3081, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15518 p hg
    simpa only [d8111, d3081, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47265 (p : Pattern) (guard : d8112 p = 1) : d3082 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3082, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47262 p hg
    simpa only [d8112, d3082, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3082, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47264 p hg
    simpa only [d8112, d3082, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47266 (p : Pattern) (guard : d8113 p = 1) : d3083 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3083, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47260 p hg
    simpa only [d8113, d3083, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3083, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47265 p hg
    simpa only [d8113, d3083, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47267 (p : Pattern) (guard : d8100 p = 1) : d2948 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2948, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35446 p hg
    simpa only [d8100, d2948, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2948, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39562 p hg
    simpa only [d8100, d2948, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47268 (p : Pattern) (guard : d8106 p = 1) : d2949 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2949, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47267 p hg
    simpa only [d8106, d2949, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2949, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d8106, d2949, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47269 (p : Pattern) (guard : d8105 p = 1) : d3080 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8105, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d8105, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47270 (p : Pattern) (guard : d8111 p = 1) : d3081 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47269 p hg
    simpa only [d8111, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15518 p hg
    simpa only [d8111, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47271 (p : Pattern) (guard : d8112 p = 1) : d3082 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3082, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47268 p hg
    simpa only [d8112, d3082, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3082, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47270 p hg
    simpa only [d8112, d3082, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47272 (p : Pattern) (guard : d8118 p = 1) : d3084 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3084, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47271 p hg
    simpa only [d8118, d3084, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3084, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46722 p hg
    simpa only [d8118, d3084, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47273 (p : Pattern) (guard : d8119 p = 1) : d3085 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3085, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47266 p hg
    simpa only [d8119, d3085, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3085, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47272 p hg
    simpa only [d8119, d3085, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47274 (p : Pattern) (guard : d8111 p = 1) : d3086 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46696 p hg
    simpa only [d8111, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d8111, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47275 (p : Pattern) (guard : d8112 p = 1) : d3087 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3087, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46627 p hg
    simpa only [d8112, d3087, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3087, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47274 p hg
    simpa only [d8112, d3087, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47276 (p : Pattern) (guard : d8111 p = 1) : d3088 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46696 p hg
    simpa only [d8111, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d8111, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47277 (p : Pattern) (guard : d0 p = 1) : d3089 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47278 (p : Pattern) (guard : d8117 p = 1) : d3090 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47276 p hg
    simpa only [d8117, d3090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47277 p hg
    simpa only [d8117, d3090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47279 (p : Pattern) (guard : d8118 p = 1) : d3091 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3091, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47275 p hg
    simpa only [d8118, d3091, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3091, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47278 p hg
    simpa only [d8118, d3091, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47280 (p : Pattern) (guard : d8117 p = 1) : d3092 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46697 p hg
    simpa only [d8117, d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47277 p hg
    simpa only [d8117, d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47281 (p : Pattern) (guard : d8123 p = 1) : d3093 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47280 p hg
    simpa only [d8123, d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46704 p hg
    simpa only [d8123, d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47282 (p : Pattern) (guard : d8124 p = 1) : d3094 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3094, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47279 p hg
    simpa only [d8124, d3094, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3094, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47281 p hg
    simpa only [d8124, d3094, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47283 (p : Pattern) (guard : d8125 p = 1) : d3095 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3095, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47273 p hg
    simpa only [d8125, d3095, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3095, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47282 p hg
    simpa only [d8125, d3095, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47284 (p : Pattern) (guard : d8100 p = 1) : d2948 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d8100, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39562 p hg
    simpa only [d8100, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47285 (p : Pattern) (guard : d8106 p = 1) : d2949 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47284 p hg
    simpa only [d8106, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d8106, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47286 (p : Pattern) (guard : d8105 p = 1) : d3098 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3098, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35517 p hg
    simpa only [d8105, d3098, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3098, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24145 p hg
    simpa only [d8105, d3098, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47287 (p : Pattern) (guard : d8111 p = 1) : d3099 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3099, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47286 p hg
    simpa only [d8111, d3099, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3099, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15534 p hg
    simpa only [d8111, d3099, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47288 (p : Pattern) (guard : d8112 p = 1) : d3100 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3100, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47285 p hg
    simpa only [d8112, d3100, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3100, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47287 p hg
    simpa only [d8112, d3100, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47289 (p : Pattern) (guard : d8105 p = 1) : d3080 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3080, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35524 p hg
    simpa only [d8105, d3080, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3080, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d8105, d3080, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47290 (p : Pattern) (guard : d8111 p = 1) : d3081 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3081, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47289 p hg
    simpa only [d8111, d3081, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3081, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15518 p hg
    simpa only [d8111, d3081, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47291 (p : Pattern) (guard : d8117 p = 1) : d3101 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3101, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47290 p hg
    simpa only [d8117, d3101, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3101, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46735 p hg
    simpa only [d8117, d3101, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47292 (p : Pattern) (guard : d8118 p = 1) : d3102 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3102, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47288 p hg
    simpa only [d8118, d3102, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3102, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47291 p hg
    simpa only [d8118, d3102, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47293 (p : Pattern) (guard : d8117 p = 1) : d3103 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3103, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47264 p hg
    simpa only [d8117, d3103, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3103, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d8117, d3103, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47294 (p : Pattern) (guard : d8123 p = 1) : d3104 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3104, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47293 p hg
    simpa only [d8123, d3104, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3104, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46740 p hg
    simpa only [d8123, d3104, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47295 (p : Pattern) (guard : d8124 p = 1) : d3105 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3105, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47292 p hg
    simpa only [d8124, d3105, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3105, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47294 p hg
    simpa only [d8124, d3105, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47296 (p : Pattern) (guard : d0 p = 1) : d2912 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47297 (p : Pattern) (guard : d8117 p = 1) : d3106 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47274 p hg
    simpa only [d8117, d3106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47296 p hg
    simpa only [d8117, d3106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47298 (p : Pattern) (guard : d0 p = 1) : d3107 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47299 (p : Pattern) (guard : d8123 p = 1) : d3108 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47297 p hg
    simpa only [d8123, d3108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47298 p hg
    simpa only [d8123, d3108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47300 (p : Pattern) (guard : d0 p = 1) : d3110 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47301 (p : Pattern) (guard : d8129 p = 1) : d3111 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47299 p hg
    simpa only [d8129, d3111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47300 p hg
    simpa only [d8129, d3111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47302 (p : Pattern) (guard : d8130 p = 1) : d3112 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3112, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47295 p hg
    simpa only [d8130, d3112, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3112, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47301 p hg
    simpa only [d8130, d3112, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47303 (p : Pattern) (guard : d8131 p = 1) : d3113 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3113, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47283 p hg
    simpa only [d8131, d3113, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3113, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47302 p hg
    simpa only [d8131, d3113, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47304 (p : Pattern) (guard : d8100 p = 1) : d3114 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3114, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35446 p hg
    simpa only [d8100, d3114, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3114, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38950 p hg
    simpa only [d8100, d3114, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47305 (p : Pattern) (guard : d8106 p = 1) : d3115 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3115, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47304 p hg
    simpa only [d8106, d3115, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3115, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39563 p hg
    simpa only [d8106, d3115, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47306 (p : Pattern) (guard : d8105 p = 1) : d2906 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8105, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23891 p hg
    simpa only [d8105, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47307 (p : Pattern) (guard : d8111 p = 1) : d3116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47306 p hg
    simpa only [d8111, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15552 p hg
    simpa only [d8111, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47308 (p : Pattern) (guard : d8112 p = 1) : d3117 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47305 p hg
    simpa only [d8112, d3117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47307 p hg
    simpa only [d8112, d3117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47309 (p : Pattern) (guard : d0 p = 1) : d2963 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47310 (p : Pattern) (guard : d8117 p = 1) : d2964 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46733 p hg
    simpa only [d8117, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47309 p hg
    simpa only [d8117, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47311 (p : Pattern) (guard : d8118 p = 1) : d3118 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47308 p hg
    simpa only [d8118, d3118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47310 p hg
    simpa only [d8118, d3118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47312 (p : Pattern) (guard : d8123 p = 1) : d2965 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47310 p hg
    simpa only [d8123, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46740 p hg
    simpa only [d8123, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47313 (p : Pattern) (guard : d8124 p = 1) : d3119 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3119, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47311 p hg
    simpa only [d8124, d3119, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3119, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47312 p hg
    simpa only [d8124, d3119, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47314 (p : Pattern) (guard : d0 p = 1) : d3121 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47315 (p : Pattern) (guard : d8117 p = 1) : d3122 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d8117, d3122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47314 p hg
    simpa only [d8117, d3122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47316 (p : Pattern) (guard : d8123 p = 1) : d3123 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47315 p hg
    simpa only [d8123, d3123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47317 (p : Pattern) (guard : d8129 p = 1) : d3124 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47316 p hg
    simpa only [d8129, d3124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47318 (p : Pattern) (guard : d8130 p = 1) : d3125 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3125, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47313 p hg
    simpa only [d8130, d3125, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3125, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47317 p hg
    simpa only [d8130, d3125, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47319 (p : Pattern) (guard : d8111 p = 1) : d3126 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3126, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47213 p hg
    simpa only [d8111, d3126, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3126, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15565 p hg
    simpa only [d8111, d3126, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
