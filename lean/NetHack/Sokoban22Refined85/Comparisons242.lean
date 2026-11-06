/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons241
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33880 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d379 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33879 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33816 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33881 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33880 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33817 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33882 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33881 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33855 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33883 (p : Pattern) (guard : d8087 p = 1) : d0 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33882 p hg
    simpa only [d8087, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d8087, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33884 (p : Pattern) (guard : d8092 p = 1) : d0 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33883 p hg
    simpa only [d8092, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33857 p hg
    simpa only [d8092, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33885 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33844 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33821 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33886 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33885 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33887 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33886 p hg
    simpa only [d8096, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33838 p hg
    simpa only [d8096, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33888 (p : Pattern) (guard : d8097 p = 1) : d0 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33884 p hg
    simpa only [d8097, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33887 p hg
    simpa only [d8097, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33889 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33865 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33821 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33890 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33889 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33891 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33890 p hg
    simpa only [d8096, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33838 p hg
    simpa only [d8096, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33892 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33893 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33854 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33894 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33895 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33893 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33894 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33896 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33897 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33898 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33899 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33897 p hg
    simpa only [d8101, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d8101, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33900 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33891 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33899 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33901 (p : Pattern) (guard : d8103 p = 1) : d0 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33888 p hg
    simpa only [d8103, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d8103, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33902 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33817 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33903 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33902 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33894 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33904 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33903 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33905 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33904 p hg
    simpa only [d8101, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d8101, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33906 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33905 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33907 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33813 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33908 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33907 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33894 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33909 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33908 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33910 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33909 p hg
    simpa only [d8101, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d8101, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33911 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33912 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33910 p hg
    simpa only [d8107, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33911 p hg
    simpa only [d8107, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33913 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33906 p hg
    simpa only [d8108, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33912 p hg
    simpa only [d8108, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33914 (p : Pattern) (guard : d8109 p = 1) : d0 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33901 p hg
    simpa only [d8109, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33913 p hg
    simpa only [d8109, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33915 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33851 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33910 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33916 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33915 p hg
    simpa only [d8108, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33875 p hg
    simpa only [d8108, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33917 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33918 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33916 p hg
    simpa only [d8114, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33917 p hg
    simpa only [d8114, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33919 (p : Pattern) (guard : d8115 p = 1) : d0 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33914 p hg
    simpa only [d8115, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33918 p hg
    simpa only [d8115, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33920 (p : Pattern) (guard : d8116 p = 1) : d0 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33878 p hg
    simpa only [d8116, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33919 p hg
    simpa only [d8116, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33921 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33871 p hg
    simpa only [d8108, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33875 p hg
    simpa only [d8108, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33922 (p : Pattern) (guard : d8109 p = 1) : d0 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33861 p hg
    simpa only [d8109, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33921 p hg
    simpa only [d8109, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33923 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33876 p hg
    simpa only [d8114, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33917 p hg
    simpa only [d8114, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33924 (p : Pattern) (guard : d8115 p = 1) : d0 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33922 p hg
    simpa only [d8115, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33923 p hg
    simpa only [d8115, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33925 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33913 p hg
    simpa only [d8114, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33917 p hg
    simpa only [d8114, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33926 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33927 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33925 p hg
    simpa only [d8120, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33926 p hg
    simpa only [d8120, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33928 (p : Pattern) (guard : d8121 p = 1) : d0 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33924 p hg
    simpa only [d8121, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33927 p hg
    simpa only [d8121, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33929 (p : Pattern) (guard : d8122 p = 1) : d0 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33920 p hg
    simpa only [d8122, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33928 p hg
    simpa only [d8122, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33930 (p : Pattern) (guard : d8103 p = 1) : d0 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33840 p hg
    simpa only [d8103, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33915 p hg
    simpa only [d8103, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33931 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33860 p hg
    simpa only [d8108, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33875 p hg
    simpa only [d8108, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33932 (p : Pattern) (guard : d8109 p = 1) : d0 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33930 p hg
    simpa only [d8109, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33931 p hg
    simpa only [d8109, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33933 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33921 p hg
    simpa only [d8114, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33917 p hg
    simpa only [d8114, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33934 (p : Pattern) (guard : d8115 p = 1) : d0 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33932 p hg
    simpa only [d8115, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33933 p hg
    simpa only [d8115, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33935 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33905 p hg
    simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33911 p hg
    simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33936 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d8108, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d8108, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33937 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33938 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33912 p hg
    simpa only [d8113, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d8113, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33939 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d8114, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d8114, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33940 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d8120, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33926 p hg
    simpa only [d8120, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33941 (p : Pattern) (guard : d8121 p = 1) : d0 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33934 p hg
    simpa only [d8121, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d8121, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33942 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33931 p hg
    simpa only [d8114, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33917 p hg
    simpa only [d8114, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33943 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d8120, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33926 p hg
    simpa only [d8120, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33944 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33945 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d8119, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d8119, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33946 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33947 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33945 p hg
    simpa only [d8125, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33946 p hg
    simpa only [d8125, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33948 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33943 p hg
    simpa only [d8126, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33947 p hg
    simpa only [d8126, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33949 (p : Pattern) (guard : d8127 p = 1) : d0 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33941 p hg
    simpa only [d8127, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33948 p hg
    simpa only [d8127, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33950 (p : Pattern) (guard : d8128 p = 1) : d0 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33929 p hg
    simpa only [d8128, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33949 p hg
    simpa only [d8128, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33951 (p : Pattern) (guard : d8097 p = 1) : d0 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33891 p hg
    simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33952 (p : Pattern) (guard : d8103 p = 1) : d0 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33951 p hg
    simpa only [d8103, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33906 p hg
    simpa only [d8103, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33953 (p : Pattern) (guard : d8109 p = 1) : d0 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33952 p hg
    simpa only [d8109, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33916 p hg
    simpa only [d8109, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33954 (p : Pattern) (guard : d8115 p = 1) : d0 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33953 p hg
    simpa only [d8115, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d8115, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33955 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33797 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33956 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33955 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33894 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33957 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33956 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33958 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33957 p hg
    simpa only [d8101, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d8101, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33959 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33887 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33960 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33899 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33911 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33961 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33959 p hg
    simpa only [d8108, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33960 p hg
    simpa only [d8108, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33962 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d8113, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d8113, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33963 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33961 p hg
    simpa only [d8114, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33962 p hg
    simpa only [d8114, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33964 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33963 p hg
    simpa only [d8120, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33945 p hg
    simpa only [d8120, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33965 (p : Pattern) (guard : d8121 p = 1) : d0 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d8121, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33964 p hg
    simpa only [d8121, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33966 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33918 p hg
    simpa only [d8120, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33926 p hg
    simpa only [d8120, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33967 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33962 p hg
    simpa only [d8119, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d8119, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33968 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33967 p hg
    simpa only [d8125, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33946 p hg
    simpa only [d8125, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33969 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33966 p hg
    simpa only [d8126, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33968 p hg
    simpa only [d8126, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33970 (p : Pattern) (guard : d8127 p = 1) : d0 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33965 p hg
    simpa only [d8127, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33969 p hg
    simpa only [d8127, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33971 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33960 p hg
    simpa only [d8113, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d8113, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33972 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33971 p hg
    simpa only [d8119, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d8119, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33973 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33972 p hg
    simpa only [d8125, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33946 p hg
    simpa only [d8125, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33974 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33927 p hg
    simpa only [d8126, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33973 p hg
    simpa only [d8126, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33975 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33976 (p : Pattern) (guard : d8132 p = 1) : d0 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33974 p hg
    simpa only [d8132, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33975 p hg
    simpa only [d8132, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33977 (p : Pattern) (guard : d8133 p = 1) : d0 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33970 p hg
    simpa only [d8133, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33976 p hg
    simpa only [d8133, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33978 (p : Pattern) (guard : d8134 p = 1) : d0 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33950 p hg
    simpa only [d8134, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33977 p hg
    simpa only [d8134, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33979 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d428 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33815 p hg
    simpa only [d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33980 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d429 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33979 p hg
    simpa only [d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33981 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33854 p hg
    simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33982 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33981 p hg
    simpa only [d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33803 p hg
    simpa only [d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33983 (p : Pattern) (guard : d8087 p = 1) : d0 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33982 p hg
    simpa only [d8087, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33856 p hg
    simpa only [d8087, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33984 (p : Pattern) (guard : d8092 p = 1) : d0 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33983 p hg
    simpa only [d8092, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33850 p hg
    simpa only [d8092, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33985 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33907 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33986 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33985 p hg
    simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33987 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33986 p hg
    simpa only [d8096, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33909 p hg
    simpa only [d8096, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33988 (p : Pattern) (guard : d8097 p = 1) : d0 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33987 p hg
    simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33989 (p : Pattern) (guard : d8103 p = 1) : d0 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33988 p hg
    simpa only [d8103, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33959 p hg
    simpa only [d8103, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33990 (p : Pattern) (guard : d8109 p = 1) : d0 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33989 p hg
    simpa only [d8109, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d8109, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33991 (p : Pattern) (guard : d8115 p = 1) : d0 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33990 p hg
    simpa only [d8115, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33925 p hg
    simpa only [d8115, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33992 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33814 p hg
    simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33902 p hg
    simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33993 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33992 p hg
    simpa only [d8091, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33908 p hg
    simpa only [d8091, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33994 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33993 p hg
    simpa only [d8096, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33904 p hg
    simpa only [d8096, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33995 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33864 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33996 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33995 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33894 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33997 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33996 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33998 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33997 p hg
    simpa only [d8101, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d8101, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33999 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33994 p hg
    simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33998 p hg
    simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34000 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33800 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34001 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34000 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33894 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34002 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34001 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34003 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34002 p hg
    simpa only [d8101, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d8101, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34004 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34005 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33816 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34006 (p : Pattern) (guard : d5847 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34007 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34005 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34008 (p : Pattern) (guard : d5854 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34009 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34007 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34008 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34010 (p : Pattern) (guard : d8099 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34011 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34009 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34012 (p : Pattern) (guard : d8105 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34013 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d8106, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d8106, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34014 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34003 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34015 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33999 p hg
    simpa only [d8108, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d8108, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34016 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33811 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34017 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34018 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34017 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34008 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34019 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34018 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
