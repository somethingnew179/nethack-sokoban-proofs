/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons254
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35700 (p : Pattern) (guard : d8101 p = 1) : d105 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d105, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35698 p hg
    simpa only [d8101, d105, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d105, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35699 p hg
    simpa only [d8101, d105, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35701 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35107 p hg
    simpa only [d8084, d103, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35702 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35701 p hg
    simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35703 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35702 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35367 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35704 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35703 p hg
    simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35705 (p : Pattern) (guard : d8105 p = 1) : d104 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d104, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35368 p hg
    simpa only [d8105, d104, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d104, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d104, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35706 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35704 p hg
    simpa only [d8106, d105, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35705 p hg
    simpa only [d8106, d105, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35707 (p : Pattern) (guard : d8107 p = 1) : d105 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35700 p hg
    simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35706 p hg
    simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35708 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35121 p hg
    simpa only [d8084, d103, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35709 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35708 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35710 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35709 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35711 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35710 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35712 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35711 p hg
    simpa only [d8106, d105, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8106, d105, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35713 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35128 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35714 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35713 p hg
    simpa only [d5847, d107, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d107, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35715 (p : Pattern) (guard : d5854 p = 1) : d107 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35714 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35716 (p : Pattern) (guard : d8099 p = 1) : d107 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35715 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35717 (p : Pattern) (guard : d8105 p = 1) : d107 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35716 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35718 (p : Pattern) (guard : d8111 p = 1) : d109 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d109, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35717 p hg
    simpa only [d8111, d109, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d109, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d8111, d109, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35719 (p : Pattern) (guard : d8112 p = 1) : d110 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d110, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35712 p hg
    simpa only [d8112, d110, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d110, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35718 p hg
    simpa only [d8112, d110, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35720 (p : Pattern) (guard : d8113 p = 1) : d111 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d111, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35707 p hg
    simpa only [d8113, d111, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d111, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35719 p hg
    simpa only [d8113, d111, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35721 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1421 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35722 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35721 p hg
    simpa only [d5847, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35723 (p : Pattern) (guard : d5854 p = 1) : d107 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35722 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35724 (p : Pattern) (guard : d8099 p = 1) : d107 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35723 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35725 (p : Pattern) (guard : d8105 p = 1) : d107 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35724 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35726 (p : Pattern) (guard : d8111 p = 1) : d109 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d109, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35725 p hg
    simpa only [d8111, d109, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d109, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d8111, d109, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35727 (p : Pattern) (guard : d8112 p = 1) : d110 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d110, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35329 p hg
    simpa only [d8112, d110, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d110, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35726 p hg
    simpa only [d8112, d110, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35728 (p : Pattern) (guard : d8117 p = 1) : d112 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35226 p hg
    simpa only [d8117, d112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35729 (p : Pattern) (guard : d8118 p = 1) : d113 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d113, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35727 p hg
    simpa only [d8118, d113, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d113, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35728 p hg
    simpa only [d8118, d113, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35730 (p : Pattern) (guard : d8119 p = 1) : d114 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35720 p hg
    simpa only [d8119, d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35729 p hg
    simpa only [d8119, d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35731 (p : Pattern) (guard : d8106 p = 1) : d118 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d118, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35301 p hg
    simpa only [d8106, d118, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d118, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d118, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35732 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20134 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35733 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35732 p hg
    simpa only [d5847, d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35734 (p : Pattern) (guard : d5854 p = 1) : d103 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35733 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35735 (p : Pattern) (guard : d8099 p = 1) : d103 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35734 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35736 (p : Pattern) (guard : d8105 p = 1) : d103 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35735 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35737 (p : Pattern) (guard : d8111 p = 1) : d122 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d122, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35736 p hg
    simpa only [d8111, d122, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d122, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d8111, d122, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35738 (p : Pattern) (guard : d8112 p = 1) : d123 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d123, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35731 p hg
    simpa only [d8112, d123, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d123, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35737 p hg
    simpa only [d8112, d123, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35739 (p : Pattern) (guard : d8111 p = 1) : d124 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d124, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35369 p hg
    simpa only [d8111, d124, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d124, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d124, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35740 (p : Pattern) (guard : d8117 p = 1) : d126 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d126, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35739 p hg
    simpa only [d8117, d126, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d126, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d8117, d126, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35741 (p : Pattern) (guard : d8118 p = 1) : d127 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d127, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35738 p hg
    simpa only [d8118, d127, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d127, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35740 p hg
    simpa only [d8118, d127, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35742 (p : Pattern) (guard : d8124 p = 1) : d130 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d130, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35741 p hg
    simpa only [d8124, d130, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d130, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d8124, d130, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35743 (p : Pattern) (guard : d8125 p = 1) : d131 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d131, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35730 p hg
    simpa only [d8125, d131, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d131, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35742 p hg
    simpa only [d8125, d131, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35744 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4578 p hg
    simpa only [d5843, d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35745 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35200 p hg
    simpa only [d8084, d103, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35744 p hg
    simpa only [d8084, d103, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35746 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35745 p hg
    simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35366 p hg
    simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35747 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35746 p hg
    simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35734 p hg
    simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35748 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35747 p hg
    simpa only [d8100, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35368 p hg
    simpa only [d8100, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35749 (p : Pattern) (guard : d8105 p = 1) : d104 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d104, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35735 p hg
    simpa only [d8105, d104, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d104, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d104, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35750 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35748 p hg
    simpa only [d8106, d105, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35749 p hg
    simpa only [d8106, d105, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35751 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35207 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35752 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35751 p hg
    simpa only [d5847, d116, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d116, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35753 (p : Pattern) (guard : d5854 p = 1) : d116 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35752 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35754 (p : Pattern) (guard : d8099 p = 1) : d116 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35753 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35755 (p : Pattern) (guard : d8105 p = 1) : d116 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35754 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35756 (p : Pattern) (guard : d8111 p = 1) : d132 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d132, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35755 p hg
    simpa only [d8111, d132, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d132, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d132, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35757 (p : Pattern) (guard : d8112 p = 1) : d133 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d133, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35750 p hg
    simpa only [d8112, d133, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d133, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35756 p hg
    simpa only [d8112, d133, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35758 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1415 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35759 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35758 p hg
    simpa only [d5847, d107, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d107, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35760 (p : Pattern) (guard : d5854 p = 1) : d107 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35759 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35761 (p : Pattern) (guard : d8099 p = 1) : d107 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35760 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35762 (p : Pattern) (guard : d8105 p = 1) : d107 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35761 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35763 (p : Pattern) (guard : d8111 p = 1) : d109 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d109, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35762 p hg
    simpa only [d8111, d109, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d109, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d8111, d109, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35764 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35765 (p : Pattern) (guard : d8117 p = 1) : d211 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d211, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35763 p hg
    simpa only [d8117, d211, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d211, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d211, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35766 (p : Pattern) (guard : d8118 p = 1) : d212 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d212, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35757 p hg
    simpa only [d8118, d212, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d212, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35765 p hg
    simpa only [d8118, d212, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35767 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35768 (p : Pattern) (guard : d8117 p = 1) : d211 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d211, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35718 p hg
    simpa only [d8117, d211, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d211, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d211, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35769 (p : Pattern) (guard : d8123 p = 1) : d213 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d213, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35768 p hg
    simpa only [d8123, d213, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d213, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d213, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35770 (p : Pattern) (guard : d8124 p = 1) : d214 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d214, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35766 p hg
    simpa only [d8124, d214, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d214, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35769 p hg
    simpa only [d8124, d214, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35771 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35084 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20134 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35772 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35771 p hg
    simpa only [d5847, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35773 (p : Pattern) (guard : d5854 p = 1) : d103 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35772 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35774 (p : Pattern) (guard : d8099 p = 1) : d103 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35773 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35775 (p : Pattern) (guard : d8105 p = 1) : d103 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35774 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35776 (p : Pattern) (guard : d8111 p = 1) : d122 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d122, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35775 p hg
    simpa only [d8111, d122, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d122, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d8111, d122, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35777 (p : Pattern) (guard : d8117 p = 1) : d140 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d140, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35776 p hg
    simpa only [d8117, d140, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d140, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d8117, d140, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35778 (p : Pattern) (guard : d0 p = 1) : d215 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35779 (p : Pattern) (guard : d8123 p = 1) : d216 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d216, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35777 p hg
    simpa only [d8123, d216, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d216, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35778 p hg
    simpa only [d8123, d216, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35780 (p : Pattern) (guard : d8129 p = 1) : d218 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d218, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35779 p hg
    simpa only [d8129, d218, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d218, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13622 p hg
    simpa only [d8129, d218, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35781 (p : Pattern) (guard : d8130 p = 1) : d219 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d219, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35770 p hg
    simpa only [d8130, d219, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d219, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35780 p hg
    simpa only [d8130, d219, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35782 (p : Pattern) (guard : d8131 p = 1) : d220 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d220, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35743 p hg
    simpa only [d8131, d220, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d220, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35781 p hg
    simpa only [d8131, d220, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35783 (p : Pattern) (guard : d8111 p = 1) : d105 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d105, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35775 p hg
    simpa only [d8111, d105, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d105, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d8111, d105, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35784 (p : Pattern) (guard : d8112 p = 1) : d105 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35329 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35783 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35785 (p : Pattern) (guard : d8111 p = 1) : d105 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d105, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35736 p hg
    simpa only [d8111, d105, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d105, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d8111, d105, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35786 (p : Pattern) (guard : d8117 p = 1) : d110 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d110, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35785 p hg
    simpa only [d8117, d110, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d110, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d8117, d110, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35787 (p : Pattern) (guard : d8118 p = 1) : d111 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d111, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35784 p hg
    simpa only [d8118, d111, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d111, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35786 p hg
    simpa only [d8118, d111, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35788 (p : Pattern) (guard : d8117 p = 1) : d110 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d110, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35370 p hg
    simpa only [d8117, d110, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d110, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d8117, d110, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35789 (p : Pattern) (guard : d8123 p = 1) : d113 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d113, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35788 p hg
    simpa only [d8123, d113, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d113, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d113, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35790 (p : Pattern) (guard : d8124 p = 1) : d114 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d114, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35787 p hg
    simpa only [d8124, d114, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d114, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35789 p hg
    simpa only [d8124, d114, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35791 (p : Pattern) (guard : d8130 p = 1) : d152 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d152, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35790 p hg
    simpa only [d8130, d152, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d152, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35363 p hg
    simpa only [d8130, d152, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35792 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35090 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20134 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35793 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35792 p hg
    simpa only [d5847, d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35794 (p : Pattern) (guard : d5854 p = 1) : d103 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35793 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35795 (p : Pattern) (guard : d8099 p = 1) : d103 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35794 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35796 (p : Pattern) (guard : d8105 p = 1) : d103 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35795 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35797 (p : Pattern) (guard : d8111 p = 1) : d105 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d105, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35796 p hg
    simpa only [d8111, d105, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d105, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d8111, d105, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35798 (p : Pattern) (guard : d8117 p = 1) : d133 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d133, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35797 p hg
    simpa only [d8117, d133, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d133, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8238 p hg
    simpa only [d8117, d133, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35799 (p : Pattern) (guard : d8123 p = 1) : d212 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d212, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35798 p hg
    simpa only [d8123, d212, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d212, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6619 p hg
    simpa only [d8123, d212, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35800 (p : Pattern) (guard : d8129 p = 1) : d214 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d214, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35799 p hg
    simpa only [d8129, d214, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d214, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3335 p hg
    simpa only [d8129, d214, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35801 (p : Pattern) (guard : d8135 p = 1) : d221 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d221, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35800 p hg
    simpa only [d8135, d221, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d221, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d8135, d221, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35802 (p : Pattern) (guard : d8136 p = 1) : d222 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d222, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35791 p hg
    simpa only [d8136, d222, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d222, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35801 p hg
    simpa only [d8136, d222, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35803 (p : Pattern) (guard : d8137 p = 1) : d223 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d223, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35782 p hg
    simpa only [d8137, d223, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d223, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35802 p hg
    simpa only [d8137, d223, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35804 (p : Pattern) (guard : d8130 p = 1) : d397 p ≤ (0 : Int) + d397 p := by
  omega
theorem compare35805 (p : Pattern) (guard : d8111 p = 1) : d345 p ≤ (0 : Int) + d345 p := by
  omega
theorem compare35806 (p : Pattern) (guard : d8117 p = 1) : d448 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d448, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35805 p hg
    simpa only [d8117, d448, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d448, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d448, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35807 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35808 (p : Pattern) (guard : d8123 p = 1) : d459 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d459, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35806 p hg
    simpa only [d8123, d459, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d459, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35807 p hg
    simpa only [d8123, d459, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35809 (p : Pattern) (guard : d8129 p = 1) : d460 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d460, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35808 p hg
    simpa only [d8129, d460, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d460, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d460, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35810 (p : Pattern) (guard : d8135 p = 1) : d461 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d461, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35809 p hg
    simpa only [d8135, d461, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d461, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d461, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35811 (p : Pattern) (guard : d8136 p = 1) : d462 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d462, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35804 p hg
    simpa only [d8136, d462, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d462, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35810 p hg
    simpa only [d8136, d462, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35812 (p : Pattern) (guard : d8141 p = 1) : d441 p ≤ (0 : Int) + d441 p := by
  omega
theorem compare35813 (p : Pattern) (guard : d8142 p = 1) : d463 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d463, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35811 p hg
    simpa only [d8142, d463, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d463, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35812 p hg
    simpa only [d8142, d463, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35814 (p : Pattern) (guard : d8143 p = 1) : d511 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d511, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35803 p hg
    simpa only [d8143, d511, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d511, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35813 p hg
    simpa only [d8143, d511, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35815 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1403 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20134 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35816 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35815 p hg
    simpa only [d5847, d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35817 (p : Pattern) (guard : d5854 p = 1) : d103 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35816 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35818 (p : Pattern) (guard : d8099 p = 1) : d103 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35817 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35819 (p : Pattern) (guard : d8105 p = 1) : d103 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35818 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35820 (p : Pattern) (guard : d8111 p = 1) : d105 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d105, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35819 p hg
    simpa only [d8111, d105, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d105, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d8111, d105, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35821 (p : Pattern) (guard : d8112 p = 1) : d105 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35706 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35820 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35822 (p : Pattern) (guard : d8117 p = 1) : d110 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d110, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35797 p hg
    simpa only [d8117, d110, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d110, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3797 p hg
    simpa only [d8117, d110, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35823 (p : Pattern) (guard : d8118 p = 1) : d111 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d111, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35821 p hg
    simpa only [d8118, d111, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d111, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35822 p hg
    simpa only [d8118, d111, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35824 (p : Pattern) (guard : d8117 p = 1) : d110 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d110, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35783 p hg
    simpa only [d8117, d110, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d110, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d8117, d110, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35825 (p : Pattern) (guard : d8123 p = 1) : d113 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d113, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35824 p hg
    simpa only [d8123, d113, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d113, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d113, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35826 (p : Pattern) (guard : d8124 p = 1) : d114 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d114, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35823 p hg
    simpa only [d8124, d114, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d114, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35825 p hg
    simpa only [d8124, d114, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35827 (p : Pattern) (guard : d8105 p = 1) : d268 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d268, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35735 p hg
    simpa only [d8105, d268, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d268, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8105, d268, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35828 (p : Pattern) (guard : d8111 p = 1) : d269 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d269, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35827 p hg
    simpa only [d8111, d269, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d269, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d269, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35829 (p : Pattern) (guard : d8117 p = 1) : d271 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d271, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35828 p hg
    simpa only [d8117, d271, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d271, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3848 p hg
    simpa only [d8117, d271, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35830 (p : Pattern) (guard : d8123 p = 1) : d276 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d276, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35829 p hg
    simpa only [d8123, d276, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d276, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4394 p hg
    simpa only [d8123, d276, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35831 (p : Pattern) (guard : d8129 p = 1) : d280 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d280, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35830 p hg
    simpa only [d8129, d280, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d280, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13990 p hg
    simpa only [d8129, d280, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35832 (p : Pattern) (guard : d8130 p = 1) : d281 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d281, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35826 p hg
    simpa only [d8130, d281, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d281, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35831 p hg
    simpa only [d8130, d281, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35833 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35143 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20134 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35834 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35833 p hg
    simpa only [d5847, d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35835 (p : Pattern) (guard : d5854 p = 1) : d103 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35834 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35836 (p : Pattern) (guard : d8099 p = 1) : d103 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35835 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35837 (p : Pattern) (guard : d8105 p = 1) : d103 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35836 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35838 (p : Pattern) (guard : d8111 p = 1) : d105 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35837 p hg
    simpa only [d8111, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d8111, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35839 (p : Pattern) (guard : d8117 p = 1) : d133 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d133, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35838 p hg
    simpa only [d8117, d133, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d133, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8272 p hg
    simpa only [d8117, d133, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
