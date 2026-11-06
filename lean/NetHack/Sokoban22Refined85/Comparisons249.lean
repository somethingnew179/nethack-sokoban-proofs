/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons248
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34860 (p : Pattern) (guard : d8099 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34861 (p : Pattern) (guard : d8100 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34862 (p : Pattern) (guard : d8106 p = 1) : d37 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d8106, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34863 (p : Pattern) (guard : d8107 p = 1) : d38 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d38, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34859 p hg
    simpa only [d8107, d38, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d38, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d8107, d38, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34864 (p : Pattern) (guard : d8106 p = 1) : d42 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d8106, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34605 p hg
    simpa only [d8106, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34865 (p : Pattern) (guard : d8105 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34866 (p : Pattern) (guard : d8111 p = 1) : d43 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d8111, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34867 (p : Pattern) (guard : d8112 p = 1) : d44 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d8112, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8112, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34868 (p : Pattern) (guard : d8113 p = 1) : d45 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d45, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d8113, d45, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d45, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d8113, d45, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34869 (p : Pattern) (guard : d8106 p = 1) : d46 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d8106, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34870 (p : Pattern) (guard : d8112 p = 1) : d47 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34869 p hg
    simpa only [d8112, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8112, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34871 (p : Pattern) (guard : d8117 p = 1) : d49 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34683 p hg
    simpa only [d8117, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34872 (p : Pattern) (guard : d8118 p = 1) : d50 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d8118, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34871 p hg
    simpa only [d8118, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34873 (p : Pattern) (guard : d8119 p = 1) : d51 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d51, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d8119, d51, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d51, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d51, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34874 (p : Pattern) (guard : d8120 p = 1) : d52 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d52, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34858 p hg
    simpa only [d8120, d52, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d52, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34873 p hg
    simpa only [d8120, d52, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34875 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34403 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34876 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34875 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34877 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34878 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34877 p hg
    simpa only [d8101, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8101, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34879 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10843 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34880 (p : Pattern) (guard : d8084 p = 1) : d31 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d8084, d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34881 (p : Pattern) (guard : d8089 p = 1) : d31 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34880 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34882 (p : Pattern) (guard : d8094 p = 1) : d31 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34883 (p : Pattern) (guard : d8100 p = 1) : d31 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34882 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34884 (p : Pattern) (guard : d8106 p = 1) : d53 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d8106, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34885 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34878 p hg
    simpa only [d8107, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34884 p hg
    simpa only [d8107, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34886 (p : Pattern) (guard : d8084 p = 1) : d18 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34624 p hg
    simpa only [d8084, d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34887 (p : Pattern) (guard : d8089 p = 1) : d18 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34886 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34888 (p : Pattern) (guard : d8094 p = 1) : d18 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34887 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34889 (p : Pattern) (guard : d8100 p = 1) : d18 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34890 (p : Pattern) (guard : d8106 p = 1) : d20 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34889 p hg
    simpa only [d8106, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34891 (p : Pattern) (guard : d8112 p = 1) : d55 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d8112, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34724 p hg
    simpa only [d8112, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34892 (p : Pattern) (guard : d8113 p = 1) : d56 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d8113, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34891 p hg
    simpa only [d8113, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34893 (p : Pattern) (guard : d8112 p = 1) : d61 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34853 p hg
    simpa only [d8112, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34727 p hg
    simpa only [d8112, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34894 (p : Pattern) (guard : d8118 p = 1) : d64 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34893 p hg
    simpa only [d8118, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34895 (p : Pattern) (guard : d8119 p = 1) : d65 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34892 p hg
    simpa only [d8119, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34894 p hg
    simpa only [d8119, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34896 (p : Pattern) (guard : d8105 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34897 (p : Pattern) (guard : d8111 p = 1) : d66 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d8111, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34898 (p : Pattern) (guard : d8112 p = 1) : d67 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d8112, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8112, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34899 (p : Pattern) (guard : d0 p = 1) : d48 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34900 (p : Pattern) (guard : d8117 p = 1) : d68 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8117, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34899 p hg
    simpa only [d8117, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34901 (p : Pattern) (guard : d8118 p = 1) : d69 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34898 p hg
    simpa only [d8118, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34902 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34903 (p : Pattern) (guard : d8117 p = 1) : d71 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8117, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34902 p hg
    simpa only [d8117, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34904 (p : Pattern) (guard : d8123 p = 1) : d74 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34903 p hg
    simpa only [d8123, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d8123, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34905 (p : Pattern) (guard : d8124 p = 1) : d75 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34901 p hg
    simpa only [d8124, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34906 (p : Pattern) (guard : d8125 p = 1) : d76 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d76, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34895 p hg
    simpa only [d8125, d76, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d76, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34905 p hg
    simpa only [d8125, d76, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34907 (p : Pattern) (guard : d8126 p = 1) : d77 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d77, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d8126, d77, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d77, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34906 p hg
    simpa only [d8126, d77, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34908 (p : Pattern) (guard : d8105 p = 1) : d15 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8105, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34909 (p : Pattern) (guard : d8106 p = 1) : d16 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d8106, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8106, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34910 (p : Pattern) (guard : d8107 p = 1) : d16 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34819 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34909 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34911 (p : Pattern) (guard : d8111 p = 1) : d20 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d8111, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d8111, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34912 (p : Pattern) (guard : d8112 p = 1) : d21 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34909 p hg
    simpa only [d8112, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8112, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34913 (p : Pattern) (guard : d8113 p = 1) : d22 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d22, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34910 p hg
    simpa only [d8113, d22, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d22, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34912 p hg
    simpa only [d8113, d22, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34914 (p : Pattern) (guard : d8117 p = 1) : d27 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34724 p hg
    simpa only [d8117, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34915 (p : Pattern) (guard : d8118 p = 1) : d28 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34912 p hg
    simpa only [d8118, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34916 (p : Pattern) (guard : d8119 p = 1) : d29 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d29, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d8119, d29, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d29, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34915 p hg
    simpa only [d8119, d29, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34917 (p : Pattern) (guard : d8105 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34709 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34918 (p : Pattern) (guard : d8111 p = 1) : d78 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34917 p hg
    simpa only [d8111, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d8111, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34919 (p : Pattern) (guard : d8112 p = 1) : d79 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8112, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34918 p hg
    simpa only [d8112, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34920 (p : Pattern) (guard : d8118 p = 1) : d80 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34919 p hg
    simpa only [d8118, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34921 (p : Pattern) (guard : d8124 p = 1) : d81 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34920 p hg
    simpa only [d8124, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34922 (p : Pattern) (guard : d8125 p = 1) : d82 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d82, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d8125, d82, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d82, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34921 p hg
    simpa only [d8125, d82, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34923 (p : Pattern) (guard : d8084 p = 1) : d14 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33811 p hg
    simpa only [d8084, d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34924 (p : Pattern) (guard : d8089 p = 1) : d14 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34923 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34925 (p : Pattern) (guard : d8094 p = 1) : d14 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34924 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34926 (p : Pattern) (guard : d8100 p = 1) : d14 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34925 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34927 (p : Pattern) (guard : d8106 p = 1) : d16 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34926 p hg
    simpa only [d8106, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8106, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34928 (p : Pattern) (guard : d8111 p = 1) : d53 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d8111, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d8111, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34929 (p : Pattern) (guard : d8112 p = 1) : d54 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34927 p hg
    simpa only [d8112, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8112, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34930 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34931 (p : Pattern) (guard : d8117 p = 1) : d55 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8117, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34930 p hg
    simpa only [d8117, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34932 (p : Pattern) (guard : d8118 p = 1) : d56 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d56, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34929 p hg
    simpa only [d8118, d56, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d56, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34931 p hg
    simpa only [d8118, d56, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34933 (p : Pattern) (guard : d8117 p = 1) : d61 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8117, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d8117, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34934 (p : Pattern) (guard : d8123 p = 1) : d64 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34933 p hg
    simpa only [d8123, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34935 (p : Pattern) (guard : d8124 p = 1) : d65 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d65, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34932 p hg
    simpa only [d8124, d65, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d65, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34934 p hg
    simpa only [d8124, d65, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34936 (p : Pattern) (guard : d8117 p = 1) : d83 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34918 p hg
    simpa only [d8117, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34937 (p : Pattern) (guard : d8123 p = 1) : d84 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34936 p hg
    simpa only [d8123, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34938 (p : Pattern) (guard : d8129 p = 1) : d85 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34937 p hg
    simpa only [d8129, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34939 (p : Pattern) (guard : d8130 p = 1) : d86 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d86, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34935 p hg
    simpa only [d8130, d86, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d86, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34938 p hg
    simpa only [d8130, d86, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34940 (p : Pattern) (guard : d8131 p = 1) : d87 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d87, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34922 p hg
    simpa only [d8131, d87, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d87, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34939 p hg
    simpa only [d8131, d87, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34941 (p : Pattern) (guard : d8132 p = 1) : d88 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d88, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34907 p hg
    simpa only [d8132, d88, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d88, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34940 p hg
    simpa only [d8132, d88, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34942 (p : Pattern) (guard : d8137 p = 1) : d444 p ≤ (0 : Int) + d444 p := by
  omega
theorem compare34943 (p : Pattern) (guard : d8138 p = 1) : d503 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d503, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34941 p hg
    simpa only [d8138, d503, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d503, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d8138, d503, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34944 (p : Pattern) (guard : d8139 p = 1) : d504 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d504, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34843 p hg
    simpa only [d8139, d504, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d504, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d8139, d504, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34945 (p : Pattern) (guard : d8140 p = 1) : d505 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d505, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34743 p hg
    simpa only [d8140, d505, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d505, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d8140, d505, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34946 (p : Pattern) (guard : d8087 p = 1) : d14 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34323 p hg
    simpa only [d8087, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34518 p hg
    simpa only [d8087, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34947 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34580 p hg
    simpa only [d8091, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34948 (p : Pattern) (guard : d8092 p = 1) : d16 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d8092, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d8092, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34949 (p : Pattern) (guard : d8097 p = 1) : d16 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34782 p hg
    simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34950 (p : Pattern) (guard : d8102 p = 1) : d21 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34753 p hg
    simpa only [d8102, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34793 p hg
    simpa only [d8102, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34951 (p : Pattern) (guard : d8103 p = 1) : d22 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34949 p hg
    simpa only [d8103, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d8103, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34952 (p : Pattern) (guard : d8107 p = 1) : d27 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34490 p hg
    simpa only [d8107, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34953 (p : Pattern) (guard : d8108 p = 1) : d28 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34759 p hg
    simpa only [d8108, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34952 p hg
    simpa only [d8108, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34954 (p : Pattern) (guard : d8109 p = 1) : d29 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34951 p hg
    simpa only [d8109, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34953 p hg
    simpa only [d8109, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34955 (p : Pattern) (guard : d8096 p = 1) : d33 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34621 p hg
    simpa only [d8096, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34956 (p : Pattern) (guard : d8102 p = 1) : d38 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34955 p hg
    simpa only [d8102, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34813 p hg
    simpa only [d8102, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34957 (p : Pattern) (guard : d8101 p = 1) : d42 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34719 p hg
    simpa only [d8101, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34513 p hg
    simpa only [d8101, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34958 (p : Pattern) (guard : d8107 p = 1) : d44 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34957 p hg
    simpa only [d8107, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8107, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34959 (p : Pattern) (guard : d8108 p = 1) : d45 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d8108, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34958 p hg
    simpa only [d8108, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34960 (p : Pattern) (guard : d8101 p = 1) : d46 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34676 p hg
    simpa only [d8101, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34961 (p : Pattern) (guard : d8107 p = 1) : d47 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34960 p hg
    simpa only [d8107, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8107, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34962 (p : Pattern) (guard : d8113 p = 1) : d50 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d8113, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34649 p hg
    simpa only [d8113, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34963 (p : Pattern) (guard : d8114 p = 1) : d51 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d8114, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34962 p hg
    simpa only [d8114, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34964 (p : Pattern) (guard : d8115 p = 1) : d52 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d8115, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d8115, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34965 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34462 p hg
    simpa only [d8086, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34810 p hg
    simpa only [d8086, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34966 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d8091, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34718 p hg
    simpa only [d8091, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34967 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34811 p hg
    simpa only [d8095, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34968 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34966 p hg
    simpa only [d8096, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34967 p hg
    simpa only [d8096, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34969 (p : Pattern) (guard : d8085 p = 1) : d31 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34468 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34970 (p : Pattern) (guard : d8090 p = 1) : d31 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34969 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34971 (p : Pattern) (guard : d8095 p = 1) : d31 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34972 (p : Pattern) (guard : d8101 p = 1) : d53 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34971 p hg
    simpa only [d8101, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34973 (p : Pattern) (guard : d8102 p = 1) : d54 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d8102, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34972 p hg
    simpa only [d8102, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34974 (p : Pattern) (guard : d8085 p = 1) : d18 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34480 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34975 (p : Pattern) (guard : d8090 p = 1) : d18 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34974 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34976 (p : Pattern) (guard : d8095 p = 1) : d18 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34975 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34977 (p : Pattern) (guard : d8101 p = 1) : d20 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d8101, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34978 (p : Pattern) (guard : d8084 p = 1) : d24 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14548 p hg
    simpa only [d8084, d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d8084, d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34979 (p : Pattern) (guard : d8089 p = 1) : d24 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34978 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34393 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34980 (p : Pattern) (guard : d8094 p = 1) : d24 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34979 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34451 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34981 (p : Pattern) (guard : d8100 p = 1) : d24 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34530 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34982 (p : Pattern) (guard : d8106 p = 1) : d26 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34981 p hg
    simpa only [d8106, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34598 p hg
    simpa only [d8106, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34983 (p : Pattern) (guard : d8107 p = 1) : d55 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34977 p hg
    simpa only [d8107, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34982 p hg
    simpa only [d8107, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34984 (p : Pattern) (guard : d8108 p = 1) : d56 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34973 p hg
    simpa only [d8108, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34983 p hg
    simpa only [d8108, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34985 (p : Pattern) (guard : d8084 p = 1) : d58 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14598 p hg
    simpa only [d8084, d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d8084, d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34986 (p : Pattern) (guard : d8089 p = 1) : d58 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34985 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34498 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34987 (p : Pattern) (guard : d8094 p = 1) : d58 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34986 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34501 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34988 (p : Pattern) (guard : d8100 p = 1) : d58 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34987 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34536 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34989 (p : Pattern) (guard : d8106 p = 1) : d60 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34988 p hg
    simpa only [d8106, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34602 p hg
    simpa only [d8106, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34990 (p : Pattern) (guard : d8107 p = 1) : d61 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34793 p hg
    simpa only [d8107, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34989 p hg
    simpa only [d8107, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34991 (p : Pattern) (guard : d8084 p = 1) : d40 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14576 p hg
    simpa only [d8084, d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d8084, d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34992 (p : Pattern) (guard : d8089 p = 1) : d40 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34991 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34435 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34993 (p : Pattern) (guard : d8094 p = 1) : d40 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34992 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34510 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34994 (p : Pattern) (guard : d8100 p = 1) : d40 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34993 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34540 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34995 (p : Pattern) (guard : d8106 p = 1) : d62 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34994 p hg
    simpa only [d8106, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34605 p hg
    simpa only [d8106, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34996 (p : Pattern) (guard : d8112 p = 1) : d63 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34995 p hg
    simpa only [d8112, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34997 (p : Pattern) (guard : d8113 p = 1) : d64 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34990 p hg
    simpa only [d8113, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34996 p hg
    simpa only [d8113, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34998 (p : Pattern) (guard : d8114 p = 1) : d65 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34984 p hg
    simpa only [d8114, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34997 p hg
    simpa only [d8114, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34999 (p : Pattern) (guard : d8101 p = 1) : d37 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34829 p hg
    simpa only [d8101, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
