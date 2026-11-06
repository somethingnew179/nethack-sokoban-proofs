/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons247
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34720 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34719 p hg
    simpa only [d8101, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8101, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34721 (p : Pattern) (guard : d8105 p = 1) : d32 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8105, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34722 (p : Pattern) (guard : d8106 p = 1) : d53 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34679 p hg
    simpa only [d8106, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34723 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34720 p hg
    simpa only [d8107, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8107, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34724 (p : Pattern) (guard : d8111 p = 1) : d26 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34682 p hg
    simpa only [d8111, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d8111, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34725 (p : Pattern) (guard : d8112 p = 1) : d55 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d8112, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34724 p hg
    simpa only [d8112, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34726 (p : Pattern) (guard : d8113 p = 1) : d56 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34723 p hg
    simpa only [d8113, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34725 p hg
    simpa only [d8113, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34727 (p : Pattern) (guard : d8111 p = 1) : d60 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34686 p hg
    simpa only [d8111, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d8111, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34728 (p : Pattern) (guard : d8112 p = 1) : d61 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d8112, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34727 p hg
    simpa only [d8112, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34729 (p : Pattern) (guard : d8111 p = 1) : d62 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34689 p hg
    simpa only [d8111, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d8111, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34730 (p : Pattern) (guard : d8117 p = 1) : d63 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34729 p hg
    simpa only [d8117, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34731 (p : Pattern) (guard : d8118 p = 1) : d64 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34728 p hg
    simpa only [d8118, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34732 (p : Pattern) (guard : d8119 p = 1) : d65 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34726 p hg
    simpa only [d8119, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34731 p hg
    simpa only [d8119, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34733 (p : Pattern) (guard : d8112 p = 1) : d83 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34712 p hg
    simpa only [d8112, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34734 (p : Pattern) (guard : d8117 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34735 (p : Pattern) (guard : d8118 p = 1) : d84 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34733 p hg
    simpa only [d8118, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34736 (p : Pattern) (guard : d8123 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34737 (p : Pattern) (guard : d8124 p = 1) : d85 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34735 p hg
    simpa only [d8124, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34738 (p : Pattern) (guard : d8125 p = 1) : d86 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34732 p hg
    simpa only [d8125, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34737 p hg
    simpa only [d8125, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34739 (p : Pattern) (guard : d8126 p = 1) : d87 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34716 p hg
    simpa only [d8126, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34738 p hg
    simpa only [d8126, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34740 (p : Pattern) (guard : d8127 p = 1) : d88 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34695 p hg
    simpa only [d8127, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34739 p hg
    simpa only [d8127, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34741 (p : Pattern) (guard : d8132 p = 1) : d425 p ≤ (0 : Int) + d425 p := by
  omega
theorem compare34742 (p : Pattern) (guard : d8133 p = 1) : d500 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34740 p hg
    simpa only [d8133, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34741 p hg
    simpa only [d8133, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34743 (p : Pattern) (guard : d8134 p = 1) : d501 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34619 p hg
    simpa only [d8134, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34742 p hg
    simpa only [d8134, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34744 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d429 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33979 p hg
    simpa only [d14, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1519 p hg
    simpa only [d14, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34745 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34744 p hg
    simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34746 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34745 p hg
    simpa only [d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34324 p hg
    simpa only [d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34747 (p : Pattern) (guard : d8087 p = 1) : d14 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34746 p hg
    simpa only [d8087, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34415 p hg
    simpa only [d8087, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34748 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34518 p hg
    simpa only [d8091, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34749 (p : Pattern) (guard : d8092 p = 1) : d16 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d16, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34747 p hg
    simpa only [d8092, d16, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d16, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34748 p hg
    simpa only [d8092, d16, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34750 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34349 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34674 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34751 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34750 p hg
    simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34752 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34675 p hg
    simpa only [d8095, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34753 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34751 p hg
    simpa only [d8096, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34752 p hg
    simpa only [d8096, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34754 (p : Pattern) (guard : d8097 p = 1) : d16 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34749 p hg
    simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34753 p hg
    simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34755 (p : Pattern) (guard : d8085 p = 1) : d18 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34380 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34756 (p : Pattern) (guard : d8090 p = 1) : d18 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34755 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34757 (p : Pattern) (guard : d8095 p = 1) : d18 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34756 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34758 (p : Pattern) (guard : d8101 p = 1) : d20 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34757 p hg
    simpa only [d8101, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34759 (p : Pattern) (guard : d8102 p = 1) : d21 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34655 p hg
    simpa only [d8102, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34758 p hg
    simpa only [d8102, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34760 (p : Pattern) (guard : d8103 p = 1) : d22 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d22, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34754 p hg
    simpa only [d8103, d22, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d22, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34759 p hg
    simpa only [d8103, d22, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34761 (p : Pattern) (guard : d8102 p = 1) : d21 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d21, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34622 p hg
    simpa only [d8102, d21, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d21, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34668 p hg
    simpa only [d8102, d21, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34762 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34763 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34762 p hg
    simpa only [d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34764 (p : Pattern) (guard : d8085 p = 1) : d24 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34763 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34389 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34765 (p : Pattern) (guard : d8090 p = 1) : d24 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34764 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34394 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34766 (p : Pattern) (guard : d8095 p = 1) : d24 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34765 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34452 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34767 (p : Pattern) (guard : d8101 p = 1) : d26 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34766 p hg
    simpa only [d8101, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34489 p hg
    simpa only [d8101, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34768 (p : Pattern) (guard : d8107 p = 1) : d27 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d27, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34767 p hg
    simpa only [d8107, d27, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d27, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d27, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34769 (p : Pattern) (guard : d8108 p = 1) : d28 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d28, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34761 p hg
    simpa only [d8108, d28, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d28, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34768 p hg
    simpa only [d8108, d28, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34770 (p : Pattern) (guard : d8109 p = 1) : d29 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d29, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34760 p hg
    simpa only [d8109, d29, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d29, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34769 p hg
    simpa only [d8109, d29, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34771 (p : Pattern) (guard : d8096 p = 1) : d33 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d33, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34581 p hg
    simpa only [d8096, d33, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d33, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d33, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34772 (p : Pattern) (guard : d8101 p = 1) : d37 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d37, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34719 p hg
    simpa only [d8101, d37, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d37, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d37, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34773 (p : Pattern) (guard : d8102 p = 1) : d38 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d38, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34771 p hg
    simpa only [d8102, d38, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d38, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34772 p hg
    simpa only [d8102, d38, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34774 (p : Pattern) (guard : d8101 p = 1) : d42 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d42, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34676 p hg
    simpa only [d8101, d42, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d42, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34513 p hg
    simpa only [d8101, d42, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34775 (p : Pattern) (guard : d8107 p = 1) : d44 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d44, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34774 p hg
    simpa only [d8107, d44, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d44, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8107, d44, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34776 (p : Pattern) (guard : d8108 p = 1) : d45 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d45, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34773 p hg
    simpa only [d8108, d45, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d45, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34775 p hg
    simpa only [d8108, d45, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34777 (p : Pattern) (guard : d8114 p = 1) : d51 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d51, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34776 p hg
    simpa only [d8114, d51, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d51, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d8114, d51, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34778 (p : Pattern) (guard : d8115 p = 1) : d52 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d52, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34770 p hg
    simpa only [d8115, d52, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d52, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34777 p hg
    simpa only [d8115, d52, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34779 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34333 p hg
    simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34717 p hg
    simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34780 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34779 p hg
    simpa only [d8091, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34675 p hg
    simpa only [d8091, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34781 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34718 p hg
    simpa only [d8095, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34782 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34780 p hg
    simpa only [d8096, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34781 p hg
    simpa only [d8096, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34783 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1208 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34784 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34783 p hg
    simpa only [d31, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d31, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34785 (p : Pattern) (guard : d8085 p = 1) : d31 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34784 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34786 (p : Pattern) (guard : d8090 p = 1) : d31 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34785 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34787 (p : Pattern) (guard : d8095 p = 1) : d31 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34786 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34788 (p : Pattern) (guard : d8101 p = 1) : d53 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34787 p hg
    simpa only [d8101, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34789 (p : Pattern) (guard : d8102 p = 1) : d54 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d54, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34782 p hg
    simpa only [d8102, d54, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d54, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34788 p hg
    simpa only [d8102, d54, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34790 (p : Pattern) (guard : d8085 p = 1) : d18 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34356 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34791 (p : Pattern) (guard : d8090 p = 1) : d18 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34790 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34792 (p : Pattern) (guard : d8095 p = 1) : d18 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34791 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34793 (p : Pattern) (guard : d8101 p = 1) : d20 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34792 p hg
    simpa only [d8101, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34794 (p : Pattern) (guard : d8084 p = 1) : d24 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34762 p hg
    simpa only [d8084, d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d8084, d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34795 (p : Pattern) (guard : d8089 p = 1) : d24 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34794 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34393 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34796 (p : Pattern) (guard : d8094 p = 1) : d24 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34795 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34451 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34797 (p : Pattern) (guard : d8100 p = 1) : d24 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34796 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34530 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34798 (p : Pattern) (guard : d8106 p = 1) : d26 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34797 p hg
    simpa only [d8106, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34598 p hg
    simpa only [d8106, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34799 (p : Pattern) (guard : d8107 p = 1) : d55 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d55, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34793 p hg
    simpa only [d8107, d55, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d55, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34798 p hg
    simpa only [d8107, d55, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34800 (p : Pattern) (guard : d8108 p = 1) : d56 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d56, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34789 p hg
    simpa only [d8108, d56, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d56, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34799 p hg
    simpa only [d8108, d56, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34801 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34802 (p : Pattern) (guard : d8084 p = 1) : d58 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d58, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34801 p hg
    simpa only [d8084, d58, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d58, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d8084, d58, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34803 (p : Pattern) (guard : d8089 p = 1) : d58 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34802 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34498 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34804 (p : Pattern) (guard : d8094 p = 1) : d58 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34803 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34501 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34805 (p : Pattern) (guard : d8100 p = 1) : d58 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34804 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34536 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34806 (p : Pattern) (guard : d8106 p = 1) : d60 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d60, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34805 p hg
    simpa only [d8106, d60, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d60, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34602 p hg
    simpa only [d8106, d60, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34807 (p : Pattern) (guard : d8107 p = 1) : d61 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d61, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34758 p hg
    simpa only [d8107, d61, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d61, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34806 p hg
    simpa only [d8107, d61, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34808 (p : Pattern) (guard : d8113 p = 1) : d64 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d64, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34807 p hg
    simpa only [d8113, d64, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d64, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d64, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34809 (p : Pattern) (guard : d8114 p = 1) : d65 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d65, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34800 p hg
    simpa only [d8114, d65, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d65, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34808 p hg
    simpa only [d8114, d65, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34810 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34811 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34810 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34812 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34811 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34813 (p : Pattern) (guard : d8101 p = 1) : d37 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34812 p hg
    simpa only [d8101, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34814 (p : Pattern) (guard : d8107 p = 1) : d67 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d67, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34813 p hg
    simpa only [d8107, d67, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d67, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34680 p hg
    simpa only [d8107, d67, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34815 (p : Pattern) (guard : d8113 p = 1) : d69 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d69, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34814 p hg
    simpa only [d8113, d69, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d69, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34684 p hg
    simpa only [d8113, d69, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34816 (p : Pattern) (guard : d8119 p = 1) : d75 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d75, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34815 p hg
    simpa only [d8119, d75, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d75, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d8119, d75, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34817 (p : Pattern) (guard : d8120 p = 1) : d76 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d76, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34809 p hg
    simpa only [d8120, d76, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d76, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34816 p hg
    simpa only [d8120, d76, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34818 (p : Pattern) (guard : d8121 p = 1) : d77 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d77, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34778 p hg
    simpa only [d8121, d77, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d77, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34817 p hg
    simpa only [d8121, d77, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34819 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34812 p hg
    simpa only [d8101, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8101, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34820 (p : Pattern) (guard : d8102 p = 1) : d16 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34622 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34819 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34821 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34720 p hg
    simpa only [d8107, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d8107, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34822 (p : Pattern) (guard : d8108 p = 1) : d22 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d22, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34820 p hg
    simpa only [d8108, d22, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d22, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34821 p hg
    simpa only [d8108, d22, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34823 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34697 p hg
    simpa only [d8107, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d8107, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34824 (p : Pattern) (guard : d8113 p = 1) : d28 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d28, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34823 p hg
    simpa only [d8113, d28, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d28, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d28, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34825 (p : Pattern) (guard : d8114 p = 1) : d29 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d29, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34822 p hg
    simpa only [d8114, d29, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d29, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34824 p hg
    simpa only [d8114, d29, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34826 (p : Pattern) (guard : d8120 p = 1) : d82 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d82, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34825 p hg
    simpa only [d8120, d82, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d82, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34715 p hg
    simpa only [d8120, d82, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34827 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34828 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34827 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34829 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34828 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34830 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34829 p hg
    simpa only [d8101, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8101, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34831 (p : Pattern) (guard : d8084 p = 1) : d31 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34521 p hg
    simpa only [d8084, d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34832 (p : Pattern) (guard : d8089 p = 1) : d31 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34831 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34833 (p : Pattern) (guard : d8094 p = 1) : d31 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34832 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34834 (p : Pattern) (guard : d8100 p = 1) : d31 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34833 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34835 (p : Pattern) (guard : d8106 p = 1) : d53 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34834 p hg
    simpa only [d8106, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34836 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34830 p hg
    simpa only [d8107, d54, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34835 p hg
    simpa only [d8107, d54, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34837 (p : Pattern) (guard : d8113 p = 1) : d56 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d56, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34836 p hg
    simpa only [d8113, d56, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d56, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34725 p hg
    simpa only [d8113, d56, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34838 (p : Pattern) (guard : d8119 p = 1) : d65 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d65, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34837 p hg
    simpa only [d8119, d65, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d65, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34731 p hg
    simpa only [d8119, d65, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34839 (p : Pattern) (guard : d8125 p = 1) : d86 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d86, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34838 p hg
    simpa only [d8125, d86, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d86, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34737 p hg
    simpa only [d8125, d86, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34840 (p : Pattern) (guard : d8126 p = 1) : d87 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d87, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34826 p hg
    simpa only [d8126, d87, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d87, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34839 p hg
    simpa only [d8126, d87, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34841 (p : Pattern) (guard : d8127 p = 1) : d88 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d88, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34818 p hg
    simpa only [d8127, d88, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d88, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34840 p hg
    simpa only [d8127, d88, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34842 (p : Pattern) (guard : d8132 p = 1) : d442 p ≤ (0 : Int) + d442 p := by
  omega
theorem compare34843 (p : Pattern) (guard : d8133 p = 1) : d502 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d502, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34841 p hg
    simpa only [d8133, d502, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d502, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34842 p hg
    simpa only [d8133, d502, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34844 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34321 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34845 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34844 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34846 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34845 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34847 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34846 p hg
    simpa only [d8101, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8101, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34848 (p : Pattern) (guard : d8102 p = 1) : d16 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34753 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34847 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34849 (p : Pattern) (guard : d8084 p = 1) : d18 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34592 p hg
    simpa only [d8084, d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34850 (p : Pattern) (guard : d8089 p = 1) : d18 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34849 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34851 (p : Pattern) (guard : d8094 p = 1) : d18 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34850 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34852 (p : Pattern) (guard : d8100 p = 1) : d18 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34851 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34853 (p : Pattern) (guard : d8106 p = 1) : d20 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34852 p hg
    simpa only [d8106, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34854 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34830 p hg
    simpa only [d8107, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34853 p hg
    simpa only [d8107, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34855 (p : Pattern) (guard : d8108 p = 1) : d22 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34848 p hg
    simpa only [d8108, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34854 p hg
    simpa only [d8108, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34856 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34819 p hg
    simpa only [d8107, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d8107, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34857 (p : Pattern) (guard : d8113 p = 1) : d28 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34856 p hg
    simpa only [d8113, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34858 (p : Pattern) (guard : d8114 p = 1) : d29 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34855 p hg
    simpa only [d8114, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34857 p hg
    simpa only [d8114, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34859 (p : Pattern) (guard : d8101 p = 1) : d33 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d33, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34719 p hg
    simpa only [d8101, d33, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d33, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d33, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
