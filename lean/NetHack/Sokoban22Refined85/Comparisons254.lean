/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons253
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35560 (p : Pattern) (guard : d8143 p = 1) : d503 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d503, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35559 p hg
    simpa only [d8143, d503, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d503, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35377 p hg
    simpa only [d8143, d503, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35561 (p : Pattern) (guard : d8144 p = 1) : d504 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d504, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35479 p hg
    simpa only [d8144, d504, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d504, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35560 p hg
    simpa only [d8144, d504, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35562 (p : Pattern) (guard : d8145 p = 1) : d505 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d505, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35082 p hg
    simpa only [d8145, d505, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d505, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35561 p hg
    simpa only [d8145, d505, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35563 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34320 p hg
    simpa only [d8086, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34844 p hg
    simpa only [d8086, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35564 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35563 p hg
    simpa only [d8091, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34828 p hg
    simpa only [d8091, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35565 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34845 p hg
    simpa only [d8095, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35566 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35564 p hg
    simpa only [d8096, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35565 p hg
    simpa only [d8096, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35567 (p : Pattern) (guard : d8102 p = 1) : d16 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35566 p hg
    simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35415 p hg
    simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35568 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35390 p hg
    simpa only [d8107, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35426 p hg
    simpa only [d8107, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35569 (p : Pattern) (guard : d8108 p = 1) : d22 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35567 p hg
    simpa only [d8108, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35568 p hg
    simpa only [d8108, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35570 (p : Pattern) (guard : d8112 p = 1) : d27 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34982 p hg
    simpa only [d8112, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35571 (p : Pattern) (guard : d8113 p = 1) : d28 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35397 p hg
    simpa only [d8113, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35570 p hg
    simpa only [d8113, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35572 (p : Pattern) (guard : d8114 p = 1) : d29 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35569 p hg
    simpa only [d8114, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35571 p hg
    simpa only [d8114, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35573 (p : Pattern) (guard : d8101 p = 1) : d33 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34877 p hg
    simpa only [d8101, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35574 (p : Pattern) (guard : d8107 p = 1) : d38 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35573 p hg
    simpa only [d8107, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35448 p hg
    simpa only [d8107, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35575 (p : Pattern) (guard : d8106 p = 1) : d42 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35072 p hg
    simpa only [d8106, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34605 p hg
    simpa only [d8106, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35576 (p : Pattern) (guard : d8112 p = 1) : d44 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35575 p hg
    simpa only [d8112, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8112, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35577 (p : Pattern) (guard : d8113 p = 1) : d45 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35574 p hg
    simpa only [d8113, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35576 p hg
    simpa only [d8113, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35578 (p : Pattern) (guard : d8106 p = 1) : d46 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34926 p hg
    simpa only [d8106, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35579 (p : Pattern) (guard : d8112 p = 1) : d47 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35578 p hg
    simpa only [d8112, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8112, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35580 (p : Pattern) (guard : d8118 p = 1) : d50 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35579 p hg
    simpa only [d8118, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34871 p hg
    simpa only [d8118, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35581 (p : Pattern) (guard : d8119 p = 1) : d51 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35577 p hg
    simpa only [d8119, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35580 p hg
    simpa only [d8119, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35582 (p : Pattern) (guard : d8120 p = 1) : d52 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35572 p hg
    simpa only [d8120, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35581 p hg
    simpa only [d8120, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35583 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34461 p hg
    simpa only [d8085, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35069 p hg
    simpa only [d8085, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35584 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35583 p hg
    simpa only [d8090, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35445 p hg
    simpa only [d8090, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35585 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35584 p hg
    simpa only [d8095, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35071 p hg
    simpa only [d8095, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35586 (p : Pattern) (guard : d8100 p = 1) : d15 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35446 p hg
    simpa only [d8100, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35587 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35585 p hg
    simpa only [d8101, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35586 p hg
    simpa only [d8101, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35588 (p : Pattern) (guard : d8084 p = 1) : d31 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d31, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34467 p hg
    simpa only [d8084, d31, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d31, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d31, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35589 (p : Pattern) (guard : d8089 p = 1) : d31 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35588 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35590 (p : Pattern) (guard : d8094 p = 1) : d31 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35589 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35591 (p : Pattern) (guard : d8100 p = 1) : d31 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35590 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35592 (p : Pattern) (guard : d8106 p = 1) : d53 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35591 p hg
    simpa only [d8106, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35593 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35587 p hg
    simpa only [d8107, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35592 p hg
    simpa only [d8107, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35594 (p : Pattern) (guard : d8084 p = 1) : d18 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d18, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34479 p hg
    simpa only [d8084, d18, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d18, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d18, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35595 (p : Pattern) (guard : d8089 p = 1) : d18 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35594 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35596 (p : Pattern) (guard : d8094 p = 1) : d18 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35595 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35597 (p : Pattern) (guard : d8100 p = 1) : d18 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35596 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35598 (p : Pattern) (guard : d8106 p = 1) : d20 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35597 p hg
    simpa only [d8106, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35599 (p : Pattern) (guard : d5854 p = 1) : d24 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19895 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35600 (p : Pattern) (guard : d8099 p = 1) : d24 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35599 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35601 (p : Pattern) (guard : d8105 p = 1) : d24 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35600 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35602 (p : Pattern) (guard : d8111 p = 1) : d26 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35601 p hg
    simpa only [d8111, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d8111, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35603 (p : Pattern) (guard : d8112 p = 1) : d55 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35598 p hg
    simpa only [d8112, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35602 p hg
    simpa only [d8112, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35604 (p : Pattern) (guard : d8113 p = 1) : d56 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35593 p hg
    simpa only [d8113, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35603 p hg
    simpa only [d8113, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35605 (p : Pattern) (guard : d8112 p = 1) : d61 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35426 p hg
    simpa only [d8112, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35226 p hg
    simpa only [d8112, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35606 (p : Pattern) (guard : d8117 p = 1) : d63 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35232 p hg
    simpa only [d8117, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35607 (p : Pattern) (guard : d8118 p = 1) : d64 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35605 p hg
    simpa only [d8118, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35606 p hg
    simpa only [d8118, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35608 (p : Pattern) (guard : d8119 p = 1) : d65 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35604 p hg
    simpa only [d8119, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35607 p hg
    simpa only [d8119, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35609 (p : Pattern) (guard : d8106 p = 1) : d37 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35465 p hg
    simpa only [d8106, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35610 (p : Pattern) (guard : d8111 p = 1) : d66 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35471 p hg
    simpa only [d8111, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35611 (p : Pattern) (guard : d8112 p = 1) : d67 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35609 p hg
    simpa only [d8112, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35610 p hg
    simpa only [d8112, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35612 (p : Pattern) (guard : d8118 p = 1) : d69 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35611 p hg
    simpa only [d8118, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35613 (p : Pattern) (guard : d8124 p = 1) : d75 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35612 p hg
    simpa only [d8124, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35614 (p : Pattern) (guard : d8125 p = 1) : d76 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35608 p hg
    simpa only [d8125, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35613 p hg
    simpa only [d8125, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35615 (p : Pattern) (guard : d8126 p = 1) : d77 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35582 p hg
    simpa only [d8126, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35614 p hg
    simpa only [d8126, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35616 (p : Pattern) (guard : d8107 p = 1) : d16 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35042 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35466 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35617 (p : Pattern) (guard : d8113 p = 1) : d22 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35616 p hg
    simpa only [d8113, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35494 p hg
    simpa only [d8113, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35618 (p : Pattern) (guard : d8118 p = 1) : d28 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35456 p hg
    simpa only [d8118, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35619 (p : Pattern) (guard : d8119 p = 1) : d29 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35617 p hg
    simpa only [d8119, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35618 p hg
    simpa only [d8119, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35620 (p : Pattern) (guard : d8112 p = 1) : d79 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34835 p hg
    simpa only [d8112, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34918 p hg
    simpa only [d8112, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35621 (p : Pattern) (guard : d8118 p = 1) : d80 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35620 p hg
    simpa only [d8118, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35622 (p : Pattern) (guard : d8124 p = 1) : d81 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35621 p hg
    simpa only [d8124, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35623 (p : Pattern) (guard : d8125 p = 1) : d82 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35619 p hg
    simpa only [d8125, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35622 p hg
    simpa only [d8125, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35624 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34583 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35625 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35624 p hg
    simpa only [d5847, d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35626 (p : Pattern) (guard : d5854 p = 1) : d31 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35625 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35627 (p : Pattern) (guard : d8099 p = 1) : d31 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35626 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35628 (p : Pattern) (guard : d8105 p = 1) : d31 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35627 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35629 (p : Pattern) (guard : d8111 p = 1) : d53 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35628 p hg
    simpa only [d8111, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d8111, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35630 (p : Pattern) (guard : d8112 p = 1) : d54 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35484 p hg
    simpa only [d8112, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35629 p hg
    simpa only [d8112, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35631 (p : Pattern) (guard : d8117 p = 1) : d55 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35491 p hg
    simpa only [d8117, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34930 p hg
    simpa only [d8117, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35632 (p : Pattern) (guard : d8118 p = 1) : d56 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35630 p hg
    simpa only [d8118, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35631 p hg
    simpa only [d8118, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35633 (p : Pattern) (guard : d8124 p = 1) : d65 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35632 p hg
    simpa only [d8124, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34934 p hg
    simpa only [d8124, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35634 (p : Pattern) (guard : d8130 p = 1) : d86 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35633 p hg
    simpa only [d8130, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34938 p hg
    simpa only [d8130, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35635 (p : Pattern) (guard : d8131 p = 1) : d87 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35623 p hg
    simpa only [d8131, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35634 p hg
    simpa only [d8131, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35636 (p : Pattern) (guard : d8132 p = 1) : d88 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35615 p hg
    simpa only [d8132, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35635 p hg
    simpa only [d8132, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35637 (p : Pattern) (guard : d8137 p = 1) : d413 p ≤ (0 : Int) + d413 p := by
  omega
theorem compare35638 (p : Pattern) (guard : d8138 p = 1) : d499 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35636 p hg
    simpa only [d8138, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35637 p hg
    simpa only [d8138, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35639 (p : Pattern) (guard : d8107 p = 1) : d16 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35415 p hg
    simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35513 p hg
    simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35640 (p : Pattern) (guard : d8112 p = 1) : d21 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35484 p hg
    simpa only [d8112, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35526 p hg
    simpa only [d8112, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35641 (p : Pattern) (guard : d8113 p = 1) : d22 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35639 p hg
    simpa only [d8113, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35640 p hg
    simpa only [d8113, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35642 (p : Pattern) (guard : d8118 p = 1) : d28 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35492 p hg
    simpa only [d8118, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35643 (p : Pattern) (guard : d8119 p = 1) : d29 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35641 p hg
    simpa only [d8119, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35642 p hg
    simpa only [d8119, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35644 (p : Pattern) (guard : d8106 p = 1) : d33 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35447 p hg
    simpa only [d8106, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35645 (p : Pattern) (guard : d8112 p = 1) : d38 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35644 p hg
    simpa only [d8112, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35499 p hg
    simpa only [d8112, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35646 (p : Pattern) (guard : d8118 p = 1) : d45 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35645 p hg
    simpa only [d8118, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35502 p hg
    simpa only [d8118, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35647 (p : Pattern) (guard : d8124 p = 1) : d51 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35646 p hg
    simpa only [d8124, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35506 p hg
    simpa only [d8124, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35648 (p : Pattern) (guard : d8125 p = 1) : d52 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35643 p hg
    simpa only [d8125, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35647 p hg
    simpa only [d8125, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35649 (p : Pattern) (guard : d8084 p = 1) : d14 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d14, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33842 p hg
    simpa only [d8084, d14, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d14, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d14, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35650 (p : Pattern) (guard : d8089 p = 1) : d14 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35649 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35651 (p : Pattern) (guard : d8094 p = 1) : d14 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35650 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35652 (p : Pattern) (guard : d8100 p = 1) : d14 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35651 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35653 (p : Pattern) (guard : d8106 p = 1) : d16 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35652 p hg
    simpa only [d8106, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8106, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35654 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35655 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35654 p hg
    simpa only [d5847, d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35656 (p : Pattern) (guard : d5854 p = 1) : d31 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35655 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35657 (p : Pattern) (guard : d8099 p = 1) : d31 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35656 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35658 (p : Pattern) (guard : d8105 p = 1) : d31 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35657 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35659 (p : Pattern) (guard : d8111 p = 1) : d53 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35658 p hg
    simpa only [d8111, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d8111, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35660 (p : Pattern) (guard : d8112 p = 1) : d54 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35653 p hg
    simpa only [d8112, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35659 p hg
    simpa only [d8112, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35661 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35662 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35661 p hg
    simpa only [d5847, d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35663 (p : Pattern) (guard : d5854 p = 1) : d18 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35662 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35664 (p : Pattern) (guard : d8099 p = 1) : d18 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35663 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35665 (p : Pattern) (guard : d8105 p = 1) : d18 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35664 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35666 (p : Pattern) (guard : d8111 p = 1) : d20 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35665 p hg
    simpa only [d8111, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d8111, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35667 (p : Pattern) (guard : d8117 p = 1) : d55 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35666 p hg
    simpa only [d8117, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34930 p hg
    simpa only [d8117, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35668 (p : Pattern) (guard : d8118 p = 1) : d56 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35660 p hg
    simpa only [d8118, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35667 p hg
    simpa only [d8118, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35669 (p : Pattern) (guard : d8117 p = 1) : d61 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35526 p hg
    simpa only [d8117, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d8117, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35670 (p : Pattern) (guard : d8123 p = 1) : d64 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35669 p hg
    simpa only [d8123, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35671 (p : Pattern) (guard : d8124 p = 1) : d65 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35668 p hg
    simpa only [d8124, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35670 p hg
    simpa only [d8124, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35672 (p : Pattern) (guard : d8111 p = 1) : d37 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35552 p hg
    simpa only [d8111, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d8111, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35673 (p : Pattern) (guard : d8117 p = 1) : d67 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35672 p hg
    simpa only [d8117, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35532 p hg
    simpa only [d8117, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35674 (p : Pattern) (guard : d8123 p = 1) : d69 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35673 p hg
    simpa only [d8123, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35534 p hg
    simpa only [d8123, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35675 (p : Pattern) (guard : d8129 p = 1) : d75 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35674 p hg
    simpa only [d8129, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13494 p hg
    simpa only [d8129, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35676 (p : Pattern) (guard : d8130 p = 1) : d76 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35671 p hg
    simpa only [d8130, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35675 p hg
    simpa only [d8130, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35677 (p : Pattern) (guard : d8131 p = 1) : d77 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35648 p hg
    simpa only [d8131, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35676 p hg
    simpa only [d8131, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35678 (p : Pattern) (guard : d8112 p = 1) : d16 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35466 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35553 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35679 (p : Pattern) (guard : d8118 p = 1) : d22 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35678 p hg
    simpa only [d8118, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35541 p hg
    simpa only [d8118, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35680 (p : Pattern) (guard : d8124 p = 1) : d29 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35679 p hg
    simpa only [d8124, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35543 p hg
    simpa only [d8124, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35681 (p : Pattern) (guard : d8130 p = 1) : d82 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35680 p hg
    simpa only [d8130, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35547 p hg
    simpa only [d8130, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35682 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34137 p hg
    simpa only [d5847, d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35683 (p : Pattern) (guard : d5854 p = 1) : d14 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35682 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35684 (p : Pattern) (guard : d8099 p = 1) : d14 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35683 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35685 (p : Pattern) (guard : d8105 p = 1) : d14 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35684 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35686 (p : Pattern) (guard : d8111 p = 1) : d16 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35685 p hg
    simpa only [d8111, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d8111, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35687 (p : Pattern) (guard : d8117 p = 1) : d54 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35686 p hg
    simpa only [d8117, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d8117, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35688 (p : Pattern) (guard : d8123 p = 1) : d56 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35687 p hg
    simpa only [d8123, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6474 p hg
    simpa only [d8123, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35689 (p : Pattern) (guard : d8129 p = 1) : d65 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35688 p hg
    simpa only [d8129, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d8129, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35690 (p : Pattern) (guard : d8135 p = 1) : d86 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35689 p hg
    simpa only [d8135, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4600 p hg
    simpa only [d8135, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35691 (p : Pattern) (guard : d8136 p = 1) : d87 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35681 p hg
    simpa only [d8136, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35690 p hg
    simpa only [d8136, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35692 (p : Pattern) (guard : d8137 p = 1) : d88 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35677 p hg
    simpa only [d8137, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35691 p hg
    simpa only [d8137, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35693 (p : Pattern) (guard : d8142 p = 1) : d425 p ≤ (0 : Int) + d425 p := by
  omega
theorem compare35694 (p : Pattern) (guard : d8143 p = 1) : d500 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35692 p hg
    simpa only [d8143, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35693 p hg
    simpa only [d8143, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35695 (p : Pattern) (guard : d8144 p = 1) : d501 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35638 p hg
    simpa only [d8144, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35694 p hg
    simpa only [d8144, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35696 (p : Pattern) (guard : d8085 p = 1) : d103 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35086 p hg
    simpa only [d8085, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35236 p hg
    simpa only [d8085, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35697 (p : Pattern) (guard : d8090 p = 1) : d103 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35696 p hg
    simpa only [d8090, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35273 p hg
    simpa only [d8090, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35698 (p : Pattern) (guard : d8095 p = 1) : d103 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35697 p hg
    simpa only [d8095, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35238 p hg
    simpa only [d8095, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35699 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35274 p hg
    simpa only [d8100, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
