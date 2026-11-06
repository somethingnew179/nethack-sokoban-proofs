/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons291
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40880 (p : Pattern) (guard : d8099 p = 1) : d2319 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2319, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35734 p hg
    simpa only [d8099, d2319, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2319, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2319, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40881 (p : Pattern) (guard : d8105 p = 1) : d2319 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40880 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40813 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40882 (p : Pattern) (guard : d8111 p = 1) : d2327 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2327, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40881 p hg
    simpa only [d8111, d2327, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2327, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d8111, d2327, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40883 (p : Pattern) (guard : d8117 p = 1) : d2377 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2377, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40882 p hg
    simpa only [d8117, d2377, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2377, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40866 p hg
    simpa only [d8117, d2377, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40884 (p : Pattern) (guard : d8123 p = 1) : d2378 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2378, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40883 p hg
    simpa only [d8123, d2378, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2378, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40868 p hg
    simpa only [d8123, d2378, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40885 (p : Pattern) (guard : d8129 p = 1) : d2379 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2379, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40884 p hg
    simpa only [d8129, d2379, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2379, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40870 p hg
    simpa only [d8129, d2379, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40886 (p : Pattern) (guard : d8135 p = 1) : d2383 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2383, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40885 p hg
    simpa only [d8135, d2383, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2383, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40872 p hg
    simpa only [d8135, d2383, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40887 (p : Pattern) (guard : d8136 p = 1) : d2384 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2384, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40879 p hg
    simpa only [d8136, d2384, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2384, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40886 p hg
    simpa only [d8136, d2384, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40888 (p : Pattern) (guard : d8142 p = 1) : d2399 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2399, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40887 p hg
    simpa only [d8142, d2399, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2399, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2399, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40889 (p : Pattern) (guard : d8143 p = 1) : d2400 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2400, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40875 p hg
    simpa only [d8143, d2400, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2400, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40888 p hg
    simpa only [d8143, d2400, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40890 (p : Pattern) (guard : d8144 p = 1) : d2401 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2401, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40806 p hg
    simpa only [d8144, d2401, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2401, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40889 p hg
    simpa only [d8144, d2401, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40891 (p : Pattern) (guard : d8145 p = 1) : d2402 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d2402, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40628 p hg
    simpa only [d8145, d2402, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d2402, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40890 p hg
    simpa only [d8145, d2402, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40892 (p : Pattern) (guard : d8146 p = 1) : d2403 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40510 p hg
    simpa only [d8146, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40891 p hg
    simpa only [d8146, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40893 (p : Pattern) (guard : d8086 p = 1) : d2297 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2297, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34745 p hg
    simpa only [d8086, d2297, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2297, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40629 p hg
    simpa only [d8086, d2297, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40894 (p : Pattern) (guard : d8091 p = 1) : d2298 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2298, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40893 p hg
    simpa only [d8091, d2298, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2298, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40282 p hg
    simpa only [d8091, d2298, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40895 (p : Pattern) (guard : d8095 p = 1) : d2187 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2187, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40359 p hg
    simpa only [d8095, d2187, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2187, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2187, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40896 (p : Pattern) (guard : d8096 p = 1) : d2299 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2299, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40894 p hg
    simpa only [d8096, d2299, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2299, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40895 p hg
    simpa only [d8096, d2299, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40897 (p : Pattern) (guard : d8090 p = 1) : d2193 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35386 p hg
    simpa only [d8090, d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40636 p hg
    simpa only [d8090, d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40898 (p : Pattern) (guard : d8095 p = 1) : d2194 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40897 p hg
    simpa only [d8095, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40899 (p : Pattern) (guard : d8100 p = 1) : d2187 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40475 p hg
    simpa only [d8100, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40900 (p : Pattern) (guard : d8101 p = 1) : d2195 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40898 p hg
    simpa only [d8101, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40899 p hg
    simpa only [d8101, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40901 (p : Pattern) (guard : d8102 p = 1) : d2300 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2300, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40896 p hg
    simpa only [d8102, d2300, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2300, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40900 p hg
    simpa only [d8102, d2300, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40902 (p : Pattern) (guard : d8094 p = 1) : d2196 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35393 p hg
    simpa only [d8094, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40903 (p : Pattern) (guard : d8100 p = 1) : d2196 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40902 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40904 (p : Pattern) (guard : d8106 p = 1) : d2198 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40903 p hg
    simpa only [d8106, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40236 p hg
    simpa only [d8106, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40905 (p : Pattern) (guard : d8107 p = 1) : d2202 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d8107, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40904 p hg
    simpa only [d8107, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40906 (p : Pattern) (guard : d8108 p = 1) : d2301 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2301, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40901 p hg
    simpa only [d8108, d2301, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2301, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40905 p hg
    simpa only [d8108, d2301, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40907 (p : Pattern) (guard : d8107 p = 1) : d2202 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2202, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40430 p hg
    simpa only [d8107, d2202, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2202, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40600 p hg
    simpa only [d8107, d2202, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40908 (p : Pattern) (guard : d8112 p = 1) : d2206 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2206, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40338 p hg
    simpa only [d8112, d2206, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2206, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2206, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40909 (p : Pattern) (guard : d8113 p = 1) : d2207 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2207, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40907 p hg
    simpa only [d8113, d2207, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2207, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40908 p hg
    simpa only [d8113, d2207, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40910 (p : Pattern) (guard : d8114 p = 1) : d2302 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2302, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40906 p hg
    simpa only [d8114, d2302, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2302, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40909 p hg
    simpa only [d8114, d2302, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40911 (p : Pattern) (guard : d8101 p = 1) : d2211 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2211, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40382 p hg
    simpa only [d8101, d2211, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2211, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2211, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40912 (p : Pattern) (guard : d8106 p = 1) : d2214 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2214, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40500 p hg
    simpa only [d8106, d2214, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2214, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40247 p hg
    simpa only [d8106, d2214, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40913 (p : Pattern) (guard : d8107 p = 1) : d2215 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2215, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40911 p hg
    simpa only [d8107, d2215, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2215, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40912 p hg
    simpa only [d8107, d2215, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40914 (p : Pattern) (guard : d8106 p = 1) : d2218 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2218, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40476 p hg
    simpa only [d8106, d2218, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2218, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40119 p hg
    simpa only [d8106, d2218, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40915 (p : Pattern) (guard : d8112 p = 1) : d2220 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2220, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40914 p hg
    simpa only [d8112, d2220, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2220, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40419 p hg
    simpa only [d8112, d2220, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40916 (p : Pattern) (guard : d8113 p = 1) : d2221 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2221, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40913 p hg
    simpa only [d8113, d2221, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2221, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40915 p hg
    simpa only [d8113, d2221, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40917 (p : Pattern) (guard : d8119 p = 1) : d2227 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2227, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40916 p hg
    simpa only [d8119, d2227, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2227, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40425 p hg
    simpa only [d8119, d2227, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40918 (p : Pattern) (guard : d8120 p = 1) : d2303 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2303, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40910 p hg
    simpa only [d8120, d2303, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2303, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40917 p hg
    simpa only [d8120, d2303, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40919 (p : Pattern) (guard : d8090 p = 1) : d2189 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35411 p hg
    simpa only [d8090, d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40691 p hg
    simpa only [d8090, d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40920 (p : Pattern) (guard : d8095 p = 1) : d2190 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40919 p hg
    simpa only [d8095, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40475 p hg
    simpa only [d8095, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40921 (p : Pattern) (guard : d8100 p = 1) : d2187 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40499 p hg
    simpa only [d8100, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40922 (p : Pattern) (guard : d8101 p = 1) : d2191 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40920 p hg
    simpa only [d8101, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40921 p hg
    simpa only [d8101, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40923 (p : Pattern) (guard : d8094 p = 1) : d2209 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2209, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35417 p hg
    simpa only [d8094, d2209, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2209, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2209, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40924 (p : Pattern) (guard : d8100 p = 1) : d2209 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40923 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40925 (p : Pattern) (guard : d8106 p = 1) : d2232 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2232, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40924 p hg
    simpa only [d8106, d2232, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2232, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d8106, d2232, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40926 (p : Pattern) (guard : d8107 p = 1) : d2304 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2304, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40922 p hg
    simpa only [d8107, d2304, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2304, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40925 p hg
    simpa only [d8107, d2304, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40927 (p : Pattern) (guard : d8094 p = 1) : d2196 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35423 p hg
    simpa only [d8094, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40928 (p : Pattern) (guard : d8100 p = 1) : d2196 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40927 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40929 (p : Pattern) (guard : d8106 p = 1) : d2198 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40928 p hg
    simpa only [d8106, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40236 p hg
    simpa only [d8106, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40930 (p : Pattern) (guard : d8099 p = 1) : d2203 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35429 p hg
    simpa only [d8099, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40931 (p : Pattern) (guard : d8105 p = 1) : d2203 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40930 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40215 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40932 (p : Pattern) (guard : d8111 p = 1) : d2205 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40931 p hg
    simpa only [d8111, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40259 p hg
    simpa only [d8111, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40933 (p : Pattern) (guard : d8112 p = 1) : d2234 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2234, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40929 p hg
    simpa only [d8112, d2234, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2234, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40932 p hg
    simpa only [d8112, d2234, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40934 (p : Pattern) (guard : d8113 p = 1) : d2305 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2305, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40926 p hg
    simpa only [d8113, d2305, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2305, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40933 p hg
    simpa only [d8113, d2305, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40935 (p : Pattern) (guard : d8099 p = 1) : d2236 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2236, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35437 p hg
    simpa only [d8099, d2236, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2236, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2236, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40936 (p : Pattern) (guard : d8105 p = 1) : d2236 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40935 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40220 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40937 (p : Pattern) (guard : d8111 p = 1) : d2238 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40936 p hg
    simpa only [d8111, d2238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40263 p hg
    simpa only [d8111, d2238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40938 (p : Pattern) (guard : d8112 p = 1) : d2239 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2239, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40904 p hg
    simpa only [d8112, d2239, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2239, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40937 p hg
    simpa only [d8112, d2239, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40939 (p : Pattern) (guard : d8118 p = 1) : d2242 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2242, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40938 p hg
    simpa only [d8118, d2242, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2242, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2242, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40940 (p : Pattern) (guard : d8119 p = 1) : d2306 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2306, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40934 p hg
    simpa only [d8119, d2306, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2306, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40939 p hg
    simpa only [d8119, d2306, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40941 (p : Pattern) (guard : d8106 p = 1) : d2214 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40619 p hg
    simpa only [d8106, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40247 p hg
    simpa only [d8106, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40942 (p : Pattern) (guard : d8112 p = 1) : d2245 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2245, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40941 p hg
    simpa only [d8112, d2245, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2245, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40445 p hg
    simpa only [d8112, d2245, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40943 (p : Pattern) (guard : d8118 p = 1) : d2247 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2247, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40942 p hg
    simpa only [d8118, d2247, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2247, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40448 p hg
    simpa only [d8118, d2247, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40944 (p : Pattern) (guard : d8124 p = 1) : d2253 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2253, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40943 p hg
    simpa only [d8124, d2253, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2253, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40453 p hg
    simpa only [d8124, d2253, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40945 (p : Pattern) (guard : d8125 p = 1) : d2307 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2307, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40940 p hg
    simpa only [d8125, d2307, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2307, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40944 p hg
    simpa only [d8125, d2307, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40946 (p : Pattern) (guard : d8126 p = 1) : d2308 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2308, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40918 p hg
    simpa only [d8126, d2308, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2308, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40945 p hg
    simpa only [d8126, d2308, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40947 (p : Pattern) (guard : d8107 p = 1) : d2201 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40430 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40620 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40948 (p : Pattern) (guard : d8112 p = 1) : d2202 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40501 p hg
    simpa only [d8112, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40461 p hg
    simpa only [d8112, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40949 (p : Pattern) (guard : d8113 p = 1) : d2256 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2256, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40947 p hg
    simpa only [d8113, d2256, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2256, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40948 p hg
    simpa only [d8113, d2256, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40950 (p : Pattern) (guard : d8118 p = 1) : d2207 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2207, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40614 p hg
    simpa only [d8118, d2207, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2207, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40464 p hg
    simpa only [d8118, d2207, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40951 (p : Pattern) (guard : d8119 p = 1) : d2257 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2257, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40949 p hg
    simpa only [d8119, d2257, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2257, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40950 p hg
    simpa only [d8119, d2257, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40952 (p : Pattern) (guard : d8125 p = 1) : d2262 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2262, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40951 p hg
    simpa only [d8125, d2262, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2262, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40473 p hg
    simpa only [d8125, d2262, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40953 (p : Pattern) (guard : d8094 p = 1) : d2185 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35463 p hg
    simpa only [d8094, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40954 (p : Pattern) (guard : d8100 p = 1) : d2185 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40953 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40955 (p : Pattern) (guard : d8106 p = 1) : d2201 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40954 p hg
    simpa only [d8106, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d8106, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40956 (p : Pattern) (guard : d8099 p = 1) : d2209 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35469 p hg
    simpa only [d8099, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40957 (p : Pattern) (guard : d8105 p = 1) : d2209 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40956 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40443 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40958 (p : Pattern) (guard : d8111 p = 1) : d2232 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40957 p hg
    simpa only [d8111, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40478 p hg
    simpa only [d8111, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40959 (p : Pattern) (guard : d8112 p = 1) : d2263 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2263, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40955 p hg
    simpa only [d8112, d2263, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2263, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40958 p hg
    simpa only [d8112, d2263, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40960 (p : Pattern) (guard : d8118 p = 1) : d2264 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2264, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40959 p hg
    simpa only [d8118, d2264, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2264, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40482 p hg
    simpa only [d8118, d2264, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40961 (p : Pattern) (guard : d8124 p = 1) : d2265 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2265, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40960 p hg
    simpa only [d8124, d2265, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2265, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40487 p hg
    simpa only [d8124, d2265, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40962 (p : Pattern) (guard : d8130 p = 1) : d2269 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2269, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40961 p hg
    simpa only [d8130, d2269, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2269, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40491 p hg
    simpa only [d8130, d2269, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40963 (p : Pattern) (guard : d8131 p = 1) : d2270 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2270, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40952 p hg
    simpa only [d8131, d2270, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2270, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40962 p hg
    simpa only [d8131, d2270, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40964 (p : Pattern) (guard : d8132 p = 1) : d2309 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2309, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40946 p hg
    simpa only [d8132, d2309, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2309, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40963 p hg
    simpa only [d8132, d2309, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40965 (p : Pattern) (guard : d8107 p = 1) : d2201 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40955 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40966 (p : Pattern) (guard : d8112 p = 1) : d2202 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40620 p hg
    simpa only [d8112, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40461 p hg
    simpa only [d8112, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40967 (p : Pattern) (guard : d8113 p = 1) : d2256 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40965 p hg
    simpa only [d8113, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40966 p hg
    simpa only [d8113, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40968 (p : Pattern) (guard : d8118 p = 1) : d2207 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40948 p hg
    simpa only [d8118, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40464 p hg
    simpa only [d8118, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40969 (p : Pattern) (guard : d8119 p = 1) : d2257 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40967 p hg
    simpa only [d8119, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40968 p hg
    simpa only [d8119, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40970 (p : Pattern) (guard : d8112 p = 1) : d2259 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40364 p hg
    simpa only [d8112, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40470 p hg
    simpa only [d8112, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40971 (p : Pattern) (guard : d8118 p = 1) : d2260 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40970 p hg
    simpa only [d8118, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40972 (p : Pattern) (guard : d8124 p = 1) : d2261 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40971 p hg
    simpa only [d8124, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40973 (p : Pattern) (guard : d8125 p = 1) : d2262 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40969 p hg
    simpa only [d8125, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40972 p hg
    simpa only [d8125, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40974 (p : Pattern) (guard : d8094 p = 1) : d2185 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35481 p hg
    simpa only [d8094, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40975 (p : Pattern) (guard : d8100 p = 1) : d2185 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40974 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40976 (p : Pattern) (guard : d8106 p = 1) : d2201 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40975 p hg
    simpa only [d8106, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d8106, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40977 (p : Pattern) (guard : d8099 p = 1) : d2209 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35626 p hg
    simpa only [d8099, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40978 (p : Pattern) (guard : d8105 p = 1) : d2209 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40977 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40443 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40979 (p : Pattern) (guard : d8111 p = 1) : d2232 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40978 p hg
    simpa only [d8111, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40478 p hg
    simpa only [d8111, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40980 (p : Pattern) (guard : d8112 p = 1) : d2263 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40976 p hg
    simpa only [d8112, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40979 p hg
    simpa only [d8112, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40981 (p : Pattern) (guard : d8099 p = 1) : d2196 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35488 p hg
    simpa only [d8099, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40982 (p : Pattern) (guard : d8105 p = 1) : d2196 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40981 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40417 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40983 (p : Pattern) (guard : d8111 p = 1) : d2198 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40982 p hg
    simpa only [d8111, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40460 p hg
    simpa only [d8111, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40984 (p : Pattern) (guard : d8117 p = 1) : d2234 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40983 p hg
    simpa only [d8117, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40481 p hg
    simpa only [d8117, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40985 (p : Pattern) (guard : d8118 p = 1) : d2264 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40980 p hg
    simpa only [d8118, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40984 p hg
    simpa only [d8118, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40986 (p : Pattern) (guard : d8124 p = 1) : d2265 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40985 p hg
    simpa only [d8124, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40487 p hg
    simpa only [d8124, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40987 (p : Pattern) (guard : d8130 p = 1) : d2269 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40986 p hg
    simpa only [d8130, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40491 p hg
    simpa only [d8130, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40988 (p : Pattern) (guard : d8131 p = 1) : d2270 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40973 p hg
    simpa only [d8131, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40987 p hg
    simpa only [d8131, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40989 (p : Pattern) (guard : d8112 p = 1) : d2277 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40338 p hg
    simpa only [d8112, d2277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40267 p hg
    simpa only [d8112, d2277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40990 (p : Pattern) (guard : d8118 p = 1) : d2278 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2278, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40989 p hg
    simpa only [d8118, d2278, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2278, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2278, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40991 (p : Pattern) (guard : d8123 p = 1) : d2279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8123, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40992 (p : Pattern) (guard : d8124 p = 1) : d2280 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2280, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40990 p hg
    simpa only [d8124, d2280, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2280, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40991 p hg
    simpa only [d8124, d2280, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40993 (p : Pattern) (guard : d8129 p = 1) : d2281 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40991 p hg
    simpa only [d8129, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40994 (p : Pattern) (guard : d8130 p = 1) : d2282 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2282, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40992 p hg
    simpa only [d8130, d2282, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2282, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40993 p hg
    simpa only [d8130, d2282, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40995 (p : Pattern) (guard : d8135 p = 1) : d2283 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40993 p hg
    simpa only [d8135, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40996 (p : Pattern) (guard : d8136 p = 1) : d2284 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2284, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40994 p hg
    simpa only [d8136, d2284, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2284, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40995 p hg
    simpa only [d8136, d2284, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40997 (p : Pattern) (guard : d8137 p = 1) : d2310 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2310, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40988 p hg
    simpa only [d8137, d2310, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2310, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40996 p hg
    simpa only [d8137, d2310, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40998 (p : Pattern) (guard : d8138 p = 1) : d2311 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2311, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40964 p hg
    simpa only [d8138, d2311, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2311, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40997 p hg
    simpa only [d8138, d2311, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40999 (p : Pattern) (guard : d8107 p = 1) : d2272 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40900 p hg
    simpa only [d8107, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40976 p hg
    simpa only [d8107, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41000 (p : Pattern) (guard : d8112 p = 1) : d2202 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40955 p hg
    simpa only [d8112, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40983 p hg
    simpa only [d8112, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41001 (p : Pattern) (guard : d8113 p = 1) : d2273 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40999 p hg
    simpa only [d8113, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41000 p hg
    simpa only [d8113, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41002 (p : Pattern) (guard : d8118 p = 1) : d2207 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40966 p hg
    simpa only [d8118, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40464 p hg
    simpa only [d8118, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41003 (p : Pattern) (guard : d8119 p = 1) : d2274 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41001 p hg
    simpa only [d8119, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41002 p hg
    simpa only [d8119, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41004 (p : Pattern) (guard : d8111 p = 1) : d2404 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40444 p hg
    simpa only [d8111, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40469 p hg
    simpa only [d8111, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41005 (p : Pattern) (guard : d8112 p = 1) : d2405 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2405, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40386 p hg
    simpa only [d8112, d2405, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2405, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41004 p hg
    simpa only [d8112, d2405, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41006 (p : Pattern) (guard : d8111 p = 1) : d2406 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40444 p hg
    simpa only [d8111, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40266 p hg
    simpa only [d8111, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41007 (p : Pattern) (guard : d0 p = 1) : d2407 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41008 (p : Pattern) (guard : d8117 p = 1) : d2408 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41006 p hg
    simpa only [d8117, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41007 p hg
    simpa only [d8117, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41009 (p : Pattern) (guard : d8118 p = 1) : d2409 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2409, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41005 p hg
    simpa only [d8118, d2409, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2409, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41008 p hg
    simpa only [d8118, d2409, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41010 (p : Pattern) (guard : d8117 p = 1) : d2410 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40445 p hg
    simpa only [d8117, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41007 p hg
    simpa only [d8117, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41011 (p : Pattern) (guard : d8123 p = 1) : d2411 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41010 p hg
    simpa only [d8123, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40452 p hg
    simpa only [d8123, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41012 (p : Pattern) (guard : d8124 p = 1) : d2412 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2412, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41009 p hg
    simpa only [d8124, d2412, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2412, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41011 p hg
    simpa only [d8124, d2412, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41013 (p : Pattern) (guard : d8125 p = 1) : d2413 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2413, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41003 p hg
    simpa only [d8125, d2413, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2413, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41012 p hg
    simpa only [d8125, d2413, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41014 (p : Pattern) (guard : d8094 p = 1) : d2185 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35510 p hg
    simpa only [d8094, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41015 (p : Pattern) (guard : d8100 p = 1) : d2185 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41014 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41016 (p : Pattern) (guard : d8106 p = 1) : d2201 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41015 p hg
    simpa only [d8106, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d8106, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41017 (p : Pattern) (guard : d8099 p = 1) : d2209 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35516 p hg
    simpa only [d8099, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41018 (p : Pattern) (guard : d8105 p = 1) : d2209 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41017 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40443 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41019 (p : Pattern) (guard : d8111 p = 1) : d2232 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41018 p hg
    simpa only [d8111, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40478 p hg
    simpa only [d8111, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
