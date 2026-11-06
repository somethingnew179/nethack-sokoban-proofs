/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons279
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39200 (p : Pattern) (guard : d8089 p = 1) : d1874 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1874, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35175 p hg
    simpa only [d8089, d1874, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1874, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d8089, d1874, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39201 (p : Pattern) (guard : d8094 p = 1) : d1875 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1875, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39200 p hg
    simpa only [d8094, d1875, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1875, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39147 p hg
    simpa only [d8094, d1875, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39202 (p : Pattern) (guard : d8100 p = 1) : d1876 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1876, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39201 p hg
    simpa only [d8100, d1876, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1876, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1876, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39203 (p : Pattern) (guard : d8101 p = 1) : d1917 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1917, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39199 p hg
    simpa only [d8101, d1917, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1917, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39202 p hg
    simpa only [d8101, d1917, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39204 (p : Pattern) (guard : d8100 p = 1) : d117 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d117, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35211 p hg
    simpa only [d8100, d117, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d117, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d117, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39205 (p : Pattern) (guard : d5854 p = 1) : d1920 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d5854, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17364 p hg
    simpa only [d5854, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39206 (p : Pattern) (guard : d8099 p = 1) : d1921 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39205 p hg
    simpa only [d8099, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17364 p hg
    simpa only [d8099, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39207 (p : Pattern) (guard : d8105 p = 1) : d1922 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39206 p hg
    simpa only [d8105, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39208 (p : Pattern) (guard : d8106 p = 1) : d1923 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1923, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39204 p hg
    simpa only [d8106, d1923, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1923, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39207 p hg
    simpa only [d8106, d1923, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39209 (p : Pattern) (guard : d8107 p = 1) : d1924 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1924, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39203 p hg
    simpa only [d8107, d1924, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1924, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39208 p hg
    simpa only [d8107, d1924, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39210 (p : Pattern) (guard : d8100 p = 1) : d108 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d108, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35220 p hg
    simpa only [d8100, d108, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d108, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d108, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39211 (p : Pattern) (guard : d8106 p = 1) : d1885 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1885, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39210 p hg
    simpa only [d8106, d1885, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1885, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39160 p hg
    simpa only [d8106, d1885, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39212 (p : Pattern) (guard : d8105 p = 1) : d59 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35224 p hg
    simpa only [d8105, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39213 (p : Pattern) (guard : d8111 p = 1) : d1754 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39212 p hg
    simpa only [d8111, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15307 p hg
    simpa only [d8111, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39214 (p : Pattern) (guard : d8112 p = 1) : d1925 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1925, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39211 p hg
    simpa only [d8112, d1925, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1925, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39213 p hg
    simpa only [d8112, d1925, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39215 (p : Pattern) (guard : d8113 p = 1) : d1926 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1926, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39209 p hg
    simpa only [d8113, d1926, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1926, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39214 p hg
    simpa only [d8113, d1926, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39216 (p : Pattern) (guard : d8105 p = 1) : d41 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35230 p hg
    simpa only [d8105, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39217 (p : Pattern) (guard : d8111 p = 1) : d1756 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39216 p hg
    simpa only [d8111, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d8111, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39218 (p : Pattern) (guard : d8112 p = 1) : d1927 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1927, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39161 p hg
    simpa only [d8112, d1927, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1927, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39217 p hg
    simpa only [d8112, d1927, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39219 (p : Pattern) (guard : d8118 p = 1) : d1928 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1928, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39218 p hg
    simpa only [d8118, d1928, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1928, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1928, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39220 (p : Pattern) (guard : d8119 p = 1) : d1929 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1929, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39215 p hg
    simpa only [d8119, d1929, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1929, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39219 p hg
    simpa only [d8119, d1929, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39221 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35238 p hg
    simpa only [d8100, d104, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39222 (p : Pattern) (guard : d8106 p = 1) : d1907 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39221 p hg
    simpa only [d8106, d1907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39185 p hg
    simpa only [d8106, d1907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39223 (p : Pattern) (guard : d8111 p = 1) : d1930 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8111, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39224 (p : Pattern) (guard : d8112 p = 1) : d1931 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1931, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39222 p hg
    simpa only [d8112, d1931, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1931, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39223 p hg
    simpa only [d8112, d1931, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39225 (p : Pattern) (guard : d8117 p = 1) : d1932 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39189 p hg
    simpa only [d8117, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38936 p hg
    simpa only [d8117, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39226 (p : Pattern) (guard : d8118 p = 1) : d1933 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1933, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39224 p hg
    simpa only [d8118, d1933, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1933, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39225 p hg
    simpa only [d8118, d1933, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39227 (p : Pattern) (guard : d0 p = 1) : d538 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39228 (p : Pattern) (guard : d8117 p = 1) : d1934 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39189 p hg
    simpa only [d8117, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39227 p hg
    simpa only [d8117, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39229 (p : Pattern) (guard : d8123 p = 1) : d1935 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39228 p hg
    simpa only [d8123, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39230 (p : Pattern) (guard : d8124 p = 1) : d1936 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1936, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39226 p hg
    simpa only [d8124, d1936, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1936, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39229 p hg
    simpa only [d8124, d1936, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39231 (p : Pattern) (guard : d8125 p = 1) : d1937 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1937, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39220 p hg
    simpa only [d8125, d1937, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1937, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39230 p hg
    simpa only [d8125, d1937, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39232 (p : Pattern) (guard : d8126 p = 1) : d1938 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1938, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39197 p hg
    simpa only [d8126, d1938, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1938, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39231 p hg
    simpa only [d8126, d1938, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39233 (p : Pattern) (guard : d5843 p = 1) : d1939 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39234 (p : Pattern) (guard : d5847 p = 1) : d1940 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39233 p hg
    simpa only [d5847, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39235 (p : Pattern) (guard : d8089 p = 1) : d1941 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8089, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d8089, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39236 (p : Pattern) (guard : d5854 p = 1) : d1940 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17386 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39237 (p : Pattern) (guard : d8094 p = 1) : d1942 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39235 p hg
    simpa only [d8094, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39236 p hg
    simpa only [d8094, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39238 (p : Pattern) (guard : d8100 p = 1) : d1943 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39237 p hg
    simpa only [d8100, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39239 (p : Pattern) (guard : d8101 p = 1) : d1944 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1944, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39164 p hg
    simpa only [d8101, d1944, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1944, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39238 p hg
    simpa only [d8101, d1944, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39240 (p : Pattern) (guard : d5854 p = 1) : d1947 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d5854, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17393 p hg
    simpa only [d5854, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39241 (p : Pattern) (guard : d0 p = 1) : d1950 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39242 (p : Pattern) (guard : d8099 p = 1) : d1951 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39240 p hg
    simpa only [d8099, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39241 p hg
    simpa only [d8099, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39243 (p : Pattern) (guard : d8105 p = 1) : d1952 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39242 p hg
    simpa only [d8105, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39244 (p : Pattern) (guard : d8106 p = 1) : d1953 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39221 p hg
    simpa only [d8106, d1953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39243 p hg
    simpa only [d8106, d1953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39245 (p : Pattern) (guard : d8107 p = 1) : d1954 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1954, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39239 p hg
    simpa only [d8107, d1954, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1954, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39244 p hg
    simpa only [d8107, d1954, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39246 (p : Pattern) (guard : d0 p = 1) : d1956 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39247 (p : Pattern) (guard : d8099 p = 1) : d1957 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39240 p hg
    simpa only [d8099, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39246 p hg
    simpa only [d8099, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39248 (p : Pattern) (guard : d8105 p = 1) : d1958 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39247 p hg
    simpa only [d8105, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39249 (p : Pattern) (guard : d8106 p = 1) : d1959 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1959, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35205 p hg
    simpa only [d8106, d1959, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1959, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39248 p hg
    simpa only [d8106, d1959, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39250 (p : Pattern) (guard : d8111 p = 1) : d1968 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35139 p hg
    simpa only [d8111, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15472 p hg
    simpa only [d8111, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39251 (p : Pattern) (guard : d8112 p = 1) : d1969 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39249 p hg
    simpa only [d8112, d1969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39250 p hg
    simpa only [d8112, d1969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39252 (p : Pattern) (guard : d8113 p = 1) : d1970 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39245 p hg
    simpa only [d8113, d1970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39251 p hg
    simpa only [d8113, d1970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39253 (p : Pattern) (guard : d8106 p = 1) : d1959 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1959, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35118 p hg
    simpa only [d8106, d1959, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1959, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39248 p hg
    simpa only [d8106, d1959, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39254 (p : Pattern) (guard : d8112 p = 1) : d1969 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39253 p hg
    simpa only [d8112, d1969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39250 p hg
    simpa only [d8112, d1969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39255 (p : Pattern) (guard : d8117 p = 1) : d1888 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38748 p hg
    simpa only [d8117, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39256 (p : Pattern) (guard : d8118 p = 1) : d1971 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1971, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39254 p hg
    simpa only [d8118, d1971, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1971, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39255 p hg
    simpa only [d8118, d1971, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39257 (p : Pattern) (guard : d8119 p = 1) : d1972 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1972, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39252 p hg
    simpa only [d8119, d1972, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1972, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39256 p hg
    simpa only [d8119, d1972, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39258 (p : Pattern) (guard : d5854 p = 1) : d1893 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d5854, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17334 p hg
    simpa only [d5854, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39259 (p : Pattern) (guard : d0 p = 1) : d1897 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39260 (p : Pattern) (guard : d8099 p = 1) : d1898 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39258 p hg
    simpa only [d8099, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39259 p hg
    simpa only [d8099, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39261 (p : Pattern) (guard : d8105 p = 1) : d1899 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39260 p hg
    simpa only [d8105, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39262 (p : Pattern) (guard : d8106 p = 1) : d1973 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35172 p hg
    simpa only [d8106, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d8106, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39263 (p : Pattern) (guard : d8111 p = 1) : d1974 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35184 p hg
    simpa only [d8111, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d8111, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39264 (p : Pattern) (guard : d8112 p = 1) : d1975 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39262 p hg
    simpa only [d8112, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39263 p hg
    simpa only [d8112, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39265 (p : Pattern) (guard : d8118 p = 1) : d1976 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39264 p hg
    simpa only [d8118, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39266 (p : Pattern) (guard : d8124 p = 1) : d1977 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39265 p hg
    simpa only [d8124, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39267 (p : Pattern) (guard : d8125 p = 1) : d1978 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1978, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39257 p hg
    simpa only [d8125, d1978, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1978, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39266 p hg
    simpa only [d8125, d1978, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39268 (p : Pattern) (guard : d8106 p = 1) : d1953 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35699 p hg
    simpa only [d8106, d1953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39243 p hg
    simpa only [d8106, d1953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39269 (p : Pattern) (guard : d8105 p = 1) : d117 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d117, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35281 p hg
    simpa only [d8105, d117, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d117, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d117, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39270 (p : Pattern) (guard : d8111 p = 1) : d1973 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1973, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39269 p hg
    simpa only [d8111, d1973, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1973, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d8111, d1973, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39271 (p : Pattern) (guard : d8112 p = 1) : d1979 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1979, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39268 p hg
    simpa only [d8112, d1979, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1979, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39270 p hg
    simpa only [d8112, d1979, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39272 (p : Pattern) (guard : d8117 p = 1) : d1980 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39250 p hg
    simpa only [d8117, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38975 p hg
    simpa only [d8117, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39273 (p : Pattern) (guard : d8118 p = 1) : d1981 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1981, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39271 p hg
    simpa only [d8118, d1981, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1981, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39272 p hg
    simpa only [d8118, d1981, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39274 (p : Pattern) (guard : d0 p = 1) : d1756 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39275 (p : Pattern) (guard : d8117 p = 1) : d1982 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39250 p hg
    simpa only [d8117, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39274 p hg
    simpa only [d8117, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39276 (p : Pattern) (guard : d8123 p = 1) : d1983 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39275 p hg
    simpa only [d8123, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39277 (p : Pattern) (guard : d8124 p = 1) : d1984 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1984, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39273 p hg
    simpa only [d8124, d1984, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1984, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39276 p hg
    simpa only [d8124, d1984, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39278 (p : Pattern) (guard : d8117 p = 1) : d1985 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39263 p hg
    simpa only [d8117, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39279 (p : Pattern) (guard : d8123 p = 1) : d1986 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39278 p hg
    simpa only [d8123, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39280 (p : Pattern) (guard : d8129 p = 1) : d1987 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39279 p hg
    simpa only [d8129, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39281 (p : Pattern) (guard : d8130 p = 1) : d1988 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1988, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39277 p hg
    simpa only [d8130, d1988, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1988, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39280 p hg
    simpa only [d8130, d1988, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39282 (p : Pattern) (guard : d8131 p = 1) : d1989 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1989, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39267 p hg
    simpa only [d8131, d1989, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1989, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39281 p hg
    simpa only [d8131, d1989, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39283 (p : Pattern) (guard : d8132 p = 1) : d1990 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1990, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39232 p hg
    simpa only [d8132, d1990, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1990, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39282 p hg
    simpa only [d8132, d1990, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39284 (p : Pattern) (guard : d8101 p = 1) : d1944 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1944, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39152 p hg
    simpa only [d8101, d1944, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1944, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39238 p hg
    simpa only [d8101, d1944, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39285 (p : Pattern) (guard : d8107 p = 1) : d1954 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1954, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39284 p hg
    simpa only [d8107, d1954, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1954, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39268 p hg
    simpa only [d8107, d1954, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39286 (p : Pattern) (guard : d8106 p = 1) : d1959 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1959, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39221 p hg
    simpa only [d8106, d1959, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1959, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39248 p hg
    simpa only [d8106, d1959, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39287 (p : Pattern) (guard : d8112 p = 1) : d1969 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1969, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39286 p hg
    simpa only [d8112, d1969, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1969, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39250 p hg
    simpa only [d8112, d1969, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39288 (p : Pattern) (guard : d8113 p = 1) : d1970 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1970, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39285 p hg
    simpa only [d8113, d1970, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1970, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39287 p hg
    simpa only [d8113, d1970, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39289 (p : Pattern) (guard : d8118 p = 1) : d1971 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1971, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39251 p hg
    simpa only [d8118, d1971, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1971, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39255 p hg
    simpa only [d8118, d1971, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39290 (p : Pattern) (guard : d8119 p = 1) : d1972 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1972, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39288 p hg
    simpa only [d8119, d1972, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1972, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39289 p hg
    simpa only [d8119, d1972, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39291 (p : Pattern) (guard : d8100 p = 1) : d117 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d117, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38208 p hg
    simpa only [d8100, d117, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d117, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d117, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39292 (p : Pattern) (guard : d8106 p = 1) : d1973 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1973, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39291 p hg
    simpa only [d8106, d1973, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1973, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d8106, d1973, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39293 (p : Pattern) (guard : d8112 p = 1) : d1975 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1975, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39292 p hg
    simpa only [d8112, d1975, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1975, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39263 p hg
    simpa only [d8112, d1975, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39294 (p : Pattern) (guard : d8118 p = 1) : d1976 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1976, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39293 p hg
    simpa only [d8118, d1976, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1976, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1976, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39295 (p : Pattern) (guard : d8124 p = 1) : d1977 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1977, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39294 p hg
    simpa only [d8124, d1977, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1977, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1977, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39296 (p : Pattern) (guard : d8125 p = 1) : d1978 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1978, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39290 p hg
    simpa only [d8125, d1978, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1978, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39295 p hg
    simpa only [d8125, d1978, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39297 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35300 p hg
    simpa only [d8100, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39298 (p : Pattern) (guard : d8106 p = 1) : d1953 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1953, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39297 p hg
    simpa only [d8106, d1953, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1953, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39243 p hg
    simpa only [d8106, d1953, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39299 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10938 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39300 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39299 p hg
    simpa only [d5847, d116, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d116, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39301 (p : Pattern) (guard : d5854 p = 1) : d116 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39300 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39302 (p : Pattern) (guard : d8099 p = 1) : d116 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39301 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39303 (p : Pattern) (guard : d8105 p = 1) : d117 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d117, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39302 p hg
    simpa only [d8105, d117, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d117, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d117, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39304 (p : Pattern) (guard : d8111 p = 1) : d1973 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1973, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39303 p hg
    simpa only [d8111, d1973, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1973, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d8111, d1973, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39305 (p : Pattern) (guard : d8112 p = 1) : d1979 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1979, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39298 p hg
    simpa only [d8112, d1979, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1979, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39304 p hg
    simpa only [d8112, d1979, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39306 (p : Pattern) (guard : d8105 p = 1) : d108 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d108, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35307 p hg
    simpa only [d8105, d108, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d108, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d108, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39307 (p : Pattern) (guard : d8111 p = 1) : d1968 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1968, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39306 p hg
    simpa only [d8111, d1968, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1968, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15472 p hg
    simpa only [d8111, d1968, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39308 (p : Pattern) (guard : d8117 p = 1) : d1980 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1980, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39307 p hg
    simpa only [d8117, d1980, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1980, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38975 p hg
    simpa only [d8117, d1980, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39309 (p : Pattern) (guard : d8118 p = 1) : d1981 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1981, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39305 p hg
    simpa only [d8118, d1981, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1981, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39308 p hg
    simpa only [d8118, d1981, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39310 (p : Pattern) (guard : d8124 p = 1) : d1984 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1984, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39309 p hg
    simpa only [d8124, d1984, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1984, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39276 p hg
    simpa only [d8124, d1984, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39311 (p : Pattern) (guard : d8130 p = 1) : d1988 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1988, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39310 p hg
    simpa only [d8130, d1988, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1988, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39280 p hg
    simpa only [d8130, d1988, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39312 (p : Pattern) (guard : d8131 p = 1) : d1989 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1989, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39296 p hg
    simpa only [d8131, d1989, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1989, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39311 p hg
    simpa only [d8131, d1989, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39313 (p : Pattern) (guard : d8118 p = 1) : d1991 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1991, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39169 p hg
    simpa only [d8118, d1991, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1991, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1991, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39314 (p : Pattern) (guard : d8124 p = 1) : d1992 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1992, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39313 p hg
    simpa only [d8124, d1992, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1992, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1992, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39315 (p : Pattern) (guard : d8130 p = 1) : d1993 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1993, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39314 p hg
    simpa only [d8130, d1993, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1993, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d1993, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39316 (p : Pattern) (guard : d8136 p = 1) : d1994 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1994, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39315 p hg
    simpa only [d8136, d1994, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1994, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d1994, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39317 (p : Pattern) (guard : d8137 p = 1) : d1995 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1995, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39312 p hg
    simpa only [d8137, d1995, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1995, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39316 p hg
    simpa only [d8137, d1995, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39318 (p : Pattern) (guard : d8138 p = 1) : d1996 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1996, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39283 p hg
    simpa only [d8138, d1996, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1996, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39317 p hg
    simpa only [d8138, d1996, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39319 (p : Pattern) (guard : d5854 p = 1) : d1874 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d5854, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d5854, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39320 (p : Pattern) (guard : d8099 p = 1) : d1875 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39319 p hg
    simpa only [d8099, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d8099, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39321 (p : Pattern) (guard : d8105 p = 1) : d1876 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39320 p hg
    simpa only [d8105, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39322 (p : Pattern) (guard : d8106 p = 1) : d1878 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1878, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39297 p hg
    simpa only [d8106, d1878, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1878, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d1878, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39323 (p : Pattern) (guard : d8107 p = 1) : d1878 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39150 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39322 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39324 (p : Pattern) (guard : d8106 p = 1) : d1878 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1878, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35699 p hg
    simpa only [d8106, d1878, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1878, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d1878, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39325 (p : Pattern) (guard : d8111 p = 1) : d1885 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1885, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39306 p hg
    simpa only [d8111, d1885, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1885, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d1885, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39326 (p : Pattern) (guard : d8112 p = 1) : d1886 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1886, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39324 p hg
    simpa only [d8112, d1886, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1886, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39325 p hg
    simpa only [d8112, d1886, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39327 (p : Pattern) (guard : d8113 p = 1) : d1997 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1997, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39323 p hg
    simpa only [d8113, d1997, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1997, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39326 p hg
    simpa only [d8113, d1997, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39328 (p : Pattern) (guard : d8106 p = 1) : d1878 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1878, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39221 p hg
    simpa only [d8106, d1878, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1878, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d1878, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39329 (p : Pattern) (guard : d8111 p = 1) : d1885 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35139 p hg
    simpa only [d8111, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39330 (p : Pattern) (guard : d8112 p = 1) : d1886 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1886, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39328 p hg
    simpa only [d8112, d1886, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1886, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39329 p hg
    simpa only [d8112, d1886, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39331 (p : Pattern) (guard : d8118 p = 1) : d1889 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1889, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39330 p hg
    simpa only [d8118, d1889, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1889, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39255 p hg
    simpa only [d8118, d1889, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39332 (p : Pattern) (guard : d8119 p = 1) : d1998 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1998, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39327 p hg
    simpa only [d8119, d1998, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1998, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39331 p hg
    simpa only [d8119, d1998, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39333 (p : Pattern) (guard : d8106 p = 1) : d1900 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1900, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35205 p hg
    simpa only [d8106, d1900, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1900, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d8106, d1900, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39334 (p : Pattern) (guard : d8111 p = 1) : d1907 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8111, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d8111, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39335 (p : Pattern) (guard : d8112 p = 1) : d1908 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1908, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39333 p hg
    simpa only [d8112, d1908, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1908, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39334 p hg
    simpa only [d8112, d1908, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39336 (p : Pattern) (guard : d8111 p = 1) : d1909 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8111, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39337 (p : Pattern) (guard : d0 p = 1) : d1910 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39338 (p : Pattern) (guard : d8117 p = 1) : d1911 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39336 p hg
    simpa only [d8117, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39337 p hg
    simpa only [d8117, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39339 (p : Pattern) (guard : d8118 p = 1) : d1912 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1912, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39335 p hg
    simpa only [d8118, d1912, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1912, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39338 p hg
    simpa only [d8118, d1912, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
