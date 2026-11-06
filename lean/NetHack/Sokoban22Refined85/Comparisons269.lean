/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons268
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37660 (p : Pattern) (guard : d8112 p = 1) : d3913 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3913, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37653 p hg
    simpa only [d8112, d3913, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3913, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37659 p hg
    simpa only [d8112, d3913, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37661 (p : Pattern) (guard : d8118 p = 1) : d3914 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3914, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37660 p hg
    simpa only [d8118, d3914, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3914, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37631 p hg
    simpa only [d8118, d3914, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37662 (p : Pattern) (guard : d8124 p = 1) : d3915 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3915, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37661 p hg
    simpa only [d8124, d3915, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3915, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37633 p hg
    simpa only [d8124, d3915, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37663 (p : Pattern) (guard : d8130 p = 1) : d3924 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3924, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37662 p hg
    simpa only [d8130, d3924, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3924, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37638 p hg
    simpa only [d8130, d3924, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37664 (p : Pattern) (guard : d8111 p = 1) : d3929 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3929, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37528 p hg
    simpa only [d8111, d3929, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3929, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37640 p hg
    simpa only [d8111, d3929, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37665 (p : Pattern) (guard : d8117 p = 1) : d3930 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3930, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37664 p hg
    simpa only [d8117, d3930, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3930, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37642 p hg
    simpa only [d8117, d3930, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37666 (p : Pattern) (guard : d8123 p = 1) : d3932 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3932, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37665 p hg
    simpa only [d8123, d3932, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3932, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37644 p hg
    simpa only [d8123, d3932, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37667 (p : Pattern) (guard : d8129 p = 1) : d3933 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3933, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37666 p hg
    simpa only [d8129, d3933, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3933, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37646 p hg
    simpa only [d8129, d3933, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37668 (p : Pattern) (guard : d8135 p = 1) : d3937 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3937, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37667 p hg
    simpa only [d8135, d3937, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3937, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37648 p hg
    simpa only [d8135, d3937, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37669 (p : Pattern) (guard : d8136 p = 1) : d3938 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3938, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37663 p hg
    simpa only [d8136, d3938, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3938, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37668 p hg
    simpa only [d8136, d3938, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37670 (p : Pattern) (guard : d8142 p = 1) : d3940 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3940, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37669 p hg
    simpa only [d8142, d3940, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3940, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d3940, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37671 (p : Pattern) (guard : d8143 p = 1) : d3941 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3941, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37651 p hg
    simpa only [d8143, d3941, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3941, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37670 p hg
    simpa only [d8143, d3941, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37672 (p : Pattern) (guard : d8144 p = 1) : d3942 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d3942, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37552 p hg
    simpa only [d8144, d3942, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d3942, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37671 p hg
    simpa only [d8144, d3942, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37673 (p : Pattern) (guard : d8145 p = 1) : d3943 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d3943, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36976 p hg
    simpa only [d8145, d3943, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d3943, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37672 p hg
    simpa only [d8145, d3943, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37674 (p : Pattern) (guard : d8086 p = 1) : d3542 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3542, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35870 p hg
    simpa only [d8086, d3542, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3542, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36620 p hg
    simpa only [d8086, d3542, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37675 (p : Pattern) (guard : d8085 p = 1) : d3544 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3544, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35869 p hg
    simpa only [d8085, d3544, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3544, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8085, d3544, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37676 (p : Pattern) (guard : d8090 p = 1) : d3545 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37675 p hg
    simpa only [d8090, d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36305 p hg
    simpa only [d8090, d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37677 (p : Pattern) (guard : d8091 p = 1) : d3546 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37674 p hg
    simpa only [d8091, d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37676 p hg
    simpa only [d8091, d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37678 (p : Pattern) (guard : d8085 p = 1) : d3548 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3548, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35871 p hg
    simpa only [d8085, d3548, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3548, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d8085, d3548, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37679 (p : Pattern) (guard : d8090 p = 1) : d3549 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37678 p hg
    simpa only [d8090, d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36310 p hg
    simpa only [d8090, d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37680 (p : Pattern) (guard : d8095 p = 1) : d3550 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37679 p hg
    simpa only [d8095, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37681 (p : Pattern) (guard : d8096 p = 1) : d3551 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37677 p hg
    simpa only [d8096, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37680 p hg
    simpa only [d8096, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37682 (p : Pattern) (guard : d8102 p = 1) : d3554 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37681 p hg
    simpa only [d8102, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37446 p hg
    simpa only [d8102, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37683 (p : Pattern) (guard : d8107 p = 1) : d3564 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37417 p hg
    simpa only [d8107, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37457 p hg
    simpa only [d8107, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37684 (p : Pattern) (guard : d8108 p = 1) : d3565 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37682 p hg
    simpa only [d8108, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37683 p hg
    simpa only [d8108, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37685 (p : Pattern) (guard : d8112 p = 1) : d3574 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36856 p hg
    simpa only [d8112, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37686 (p : Pattern) (guard : d8113 p = 1) : d3575 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37424 p hg
    simpa only [d8113, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37685 p hg
    simpa only [d8113, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37687 (p : Pattern) (guard : d8114 p = 1) : d3576 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37684 p hg
    simpa only [d8114, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37686 p hg
    simpa only [d8114, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37688 (p : Pattern) (guard : d8101 p = 1) : d3589 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36894 p hg
    simpa only [d8101, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d8101, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37689 (p : Pattern) (guard : d8107 p = 1) : d3596 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37688 p hg
    simpa only [d8107, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37475 p hg
    simpa only [d8107, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37690 (p : Pattern) (guard : d8106 p = 1) : d3600 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36802 p hg
    simpa only [d8106, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36239 p hg
    simpa only [d8106, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37691 (p : Pattern) (guard : d8112 p = 1) : d3607 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37690 p hg
    simpa only [d8112, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36693 p hg
    simpa only [d8112, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37692 (p : Pattern) (guard : d8113 p = 1) : d3608 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37689 p hg
    simpa only [d8113, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37691 p hg
    simpa only [d8113, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37693 (p : Pattern) (guard : d8106 p = 1) : d3609 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36774 p hg
    simpa only [d8106, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37694 (p : Pattern) (guard : d8112 p = 1) : d3610 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37693 p hg
    simpa only [d8112, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36693 p hg
    simpa only [d8112, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37695 (p : Pattern) (guard : d8118 p = 1) : d3613 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37694 p hg
    simpa only [d8118, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36698 p hg
    simpa only [d8118, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37696 (p : Pattern) (guard : d8119 p = 1) : d3614 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37692 p hg
    simpa only [d8119, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37695 p hg
    simpa only [d8119, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37697 (p : Pattern) (guard : d8120 p = 1) : d3615 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37687 p hg
    simpa only [d8120, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37696 p hg
    simpa only [d8120, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37698 (p : Pattern) (guard : d8085 p = 1) : d3617 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3617, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36044 p hg
    simpa only [d8085, d3617, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3617, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36799 p hg
    simpa only [d8085, d3617, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37699 (p : Pattern) (guard : d8090 p = 1) : d3618 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37698 p hg
    simpa only [d8090, d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36965 p hg
    simpa only [d8090, d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37700 (p : Pattern) (guard : d8089 p = 1) : d3544 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36799 p hg
    simpa only [d8089, d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d8089, d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37701 (p : Pattern) (guard : d8094 p = 1) : d3545 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37700 p hg
    simpa only [d8094, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36653 p hg
    simpa only [d8094, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37702 (p : Pattern) (guard : d8095 p = 1) : d3619 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37699 p hg
    simpa only [d8095, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37701 p hg
    simpa only [d8095, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37703 (p : Pattern) (guard : d8089 p = 1) : d3548 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36964 p hg
    simpa only [d8089, d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36309 p hg
    simpa only [d8089, d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37704 (p : Pattern) (guard : d8094 p = 1) : d3549 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37703 p hg
    simpa only [d8094, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36657 p hg
    simpa only [d8094, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37705 (p : Pattern) (guard : d8100 p = 1) : d3550 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37704 p hg
    simpa only [d8100, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37706 (p : Pattern) (guard : d8101 p = 1) : d3620 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37702 p hg
    simpa only [d8101, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37705 p hg
    simpa only [d8101, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37707 (p : Pattern) (guard : d8084 p = 1) : d30 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37708 (p : Pattern) (guard : d8089 p = 1) : d30 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37707 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37709 (p : Pattern) (guard : d8094 p = 1) : d30 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37708 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37710 (p : Pattern) (guard : d8100 p = 1) : d3623 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37709 p hg
    simpa only [d8100, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36710 p hg
    simpa only [d8100, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37711 (p : Pattern) (guard : d8106 p = 1) : d3628 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37710 p hg
    simpa only [d8106, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36714 p hg
    simpa only [d8106, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37712 (p : Pattern) (guard : d8107 p = 1) : d3629 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37706 p hg
    simpa only [d8107, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37711 p hg
    simpa only [d8107, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37713 (p : Pattern) (guard : d8084 p = 1) : d17 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare790 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37714 (p : Pattern) (guard : d8089 p = 1) : d17 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37713 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37715 (p : Pattern) (guard : d8094 p = 1) : d17 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37714 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37716 (p : Pattern) (guard : d8100 p = 1) : d3558 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37715 p hg
    simpa only [d8100, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36665 p hg
    simpa only [d8100, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37717 (p : Pattern) (guard : d8106 p = 1) : d3563 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37716 p hg
    simpa only [d8106, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36669 p hg
    simpa only [d8106, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37718 (p : Pattern) (guard : d5847 p = 1) : d23 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37719 (p : Pattern) (guard : d5854 p = 1) : d23 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37718 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37720 (p : Pattern) (guard : d8099 p = 1) : d23 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37719 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37721 (p : Pattern) (guard : d8105 p = 1) : d3568 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37720 p hg
    simpa only [d8105, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36405 p hg
    simpa only [d8105, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37722 (p : Pattern) (guard : d8111 p = 1) : d3573 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37721 p hg
    simpa only [d8111, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36722 p hg
    simpa only [d8111, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37723 (p : Pattern) (guard : d8112 p = 1) : d3630 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37717 p hg
    simpa only [d8112, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37722 p hg
    simpa only [d8112, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37724 (p : Pattern) (guard : d8113 p = 1) : d3631 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37712 p hg
    simpa only [d8113, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37723 p hg
    simpa only [d8113, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37725 (p : Pattern) (guard : d8112 p = 1) : d3637 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37457 p hg
    simpa only [d8112, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37135 p hg
    simpa only [d8112, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37726 (p : Pattern) (guard : d8117 p = 1) : d3640 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37142 p hg
    simpa only [d8117, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37727 (p : Pattern) (guard : d8118 p = 1) : d3641 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37725 p hg
    simpa only [d8118, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37726 p hg
    simpa only [d8118, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37728 (p : Pattern) (guard : d8119 p = 1) : d3642 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37724 p hg
    simpa only [d8119, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37727 p hg
    simpa only [d8119, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37729 (p : Pattern) (guard : d8106 p = 1) : d3595 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37493 p hg
    simpa only [d8106, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36451 p hg
    simpa only [d8106, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37730 (p : Pattern) (guard : d8111 p = 1) : d3644 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37499 p hg
    simpa only [d8111, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37731 (p : Pattern) (guard : d8112 p = 1) : d3645 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37729 p hg
    simpa only [d8112, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37730 p hg
    simpa only [d8112, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37732 (p : Pattern) (guard : d8118 p = 1) : d3647 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37731 p hg
    simpa only [d8118, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36735 p hg
    simpa only [d8118, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37733 (p : Pattern) (guard : d8124 p = 1) : d3653 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37732 p hg
    simpa only [d8124, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36740 p hg
    simpa only [d8124, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37734 (p : Pattern) (guard : d8125 p = 1) : d3654 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37728 p hg
    simpa only [d8125, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37733 p hg
    simpa only [d8125, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37735 (p : Pattern) (guard : d8126 p = 1) : d3655 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37697 p hg
    simpa only [d8126, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37734 p hg
    simpa only [d8126, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37736 (p : Pattern) (guard : d8132 p = 1) : d3696 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37735 p hg
    simpa only [d8132, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37541 p hg
    simpa only [d8132, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37737 (p : Pattern) (guard : d8107 p = 1) : d3666 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37555 p hg
    simpa only [d8107, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37523 p hg
    simpa only [d8107, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37738 (p : Pattern) (guard : d8106 p = 1) : d3668 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37493 p hg
    simpa only [d8106, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36753 p hg
    simpa only [d8106, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37739 (p : Pattern) (guard : d8112 p = 1) : d3671 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37738 p hg
    simpa only [d8112, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37536 p hg
    simpa only [d8112, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37740 (p : Pattern) (guard : d8113 p = 1) : d3672 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37737 p hg
    simpa only [d8113, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37739 p hg
    simpa only [d8113, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37741 (p : Pattern) (guard : d8118 p = 1) : d3676 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37511 p hg
    simpa only [d8118, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36759 p hg
    simpa only [d8118, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37742 (p : Pattern) (guard : d8119 p = 1) : d3677 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37740 p hg
    simpa only [d8119, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37741 p hg
    simpa only [d8119, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37743 (p : Pattern) (guard : d8112 p = 1) : d3681 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36628 p hg
    simpa only [d8112, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36766 p hg
    simpa only [d8112, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37744 (p : Pattern) (guard : d8118 p = 1) : d3682 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37743 p hg
    simpa only [d8118, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37745 (p : Pattern) (guard : d8124 p = 1) : d3683 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37744 p hg
    simpa only [d8124, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37746 (p : Pattern) (guard : d8125 p = 1) : d3684 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37742 p hg
    simpa only [d8125, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37745 p hg
    simpa only [d8125, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37747 (p : Pattern) (guard : d8100 p = 1) : d3582 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37590 p hg
    simpa only [d8100, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d8100, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37748 (p : Pattern) (guard : d8106 p = 1) : d3665 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37747 p hg
    simpa only [d8106, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d8106, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37749 (p : Pattern) (guard : d8105 p = 1) : d3643 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37596 p hg
    simpa only [d8105, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36730 p hg
    simpa only [d8105, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37750 (p : Pattern) (guard : d8111 p = 1) : d3678 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37749 p hg
    simpa only [d8111, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36776 p hg
    simpa only [d8111, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37751 (p : Pattern) (guard : d8112 p = 1) : d3685 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37748 p hg
    simpa only [d8112, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37750 p hg
    simpa only [d8112, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37752 (p : Pattern) (guard : d8105 p = 1) : d3605 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37605 p hg
    simpa only [d8105, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36691 p hg
    simpa only [d8105, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37753 (p : Pattern) (guard : d8111 p = 1) : d3670 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37752 p hg
    simpa only [d8111, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36755 p hg
    simpa only [d8111, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37754 (p : Pattern) (guard : d8117 p = 1) : d3686 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37753 p hg
    simpa only [d8117, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36779 p hg
    simpa only [d8117, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37755 (p : Pattern) (guard : d8118 p = 1) : d3687 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37751 p hg
    simpa only [d8118, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37754 p hg
    simpa only [d8118, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37756 (p : Pattern) (guard : d8117 p = 1) : d3688 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37536 p hg
    simpa only [d8117, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d8117, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37757 (p : Pattern) (guard : d8123 p = 1) : d3689 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37756 p hg
    simpa only [d8123, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36784 p hg
    simpa only [d8123, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37758 (p : Pattern) (guard : d8124 p = 1) : d3690 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37755 p hg
    simpa only [d8124, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37757 p hg
    simpa only [d8124, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37759 (p : Pattern) (guard : d8130 p = 1) : d3694 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37758 p hg
    simpa only [d8130, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36789 p hg
    simpa only [d8130, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37760 (p : Pattern) (guard : d8131 p = 1) : d3695 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37746 p hg
    simpa only [d8131, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37759 p hg
    simpa only [d8131, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37761 (p : Pattern) (guard : d8106 p = 1) : d3674 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36855 p hg
    simpa only [d8106, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36232 p hg
    simpa only [d8106, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37762 (p : Pattern) (guard : d8112 p = 1) : d3697 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37761 p hg
    simpa only [d8112, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36472 p hg
    simpa only [d8112, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37763 (p : Pattern) (guard : d8118 p = 1) : d3698 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37762 p hg
    simpa only [d8118, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37764 (p : Pattern) (guard : d8124 p = 1) : d3700 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37763 p hg
    simpa only [d8124, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37545 p hg
    simpa only [d8124, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37765 (p : Pattern) (guard : d8130 p = 1) : d3702 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37764 p hg
    simpa only [d8130, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37547 p hg
    simpa only [d8130, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37766 (p : Pattern) (guard : d8123 p = 1) : d3699 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37726 p hg
    simpa only [d8123, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37767 (p : Pattern) (guard : d8129 p = 1) : d3701 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37766 p hg
    simpa only [d8129, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37768 (p : Pattern) (guard : d8135 p = 1) : d3703 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37767 p hg
    simpa only [d8135, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37769 (p : Pattern) (guard : d8136 p = 1) : d3704 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37765 p hg
    simpa only [d8136, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37768 p hg
    simpa only [d8136, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37770 (p : Pattern) (guard : d8137 p = 1) : d3705 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37760 p hg
    simpa only [d8137, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37769 p hg
    simpa only [d8137, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37771 (p : Pattern) (guard : d8138 p = 1) : d3706 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37736 p hg
    simpa only [d8138, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37770 p hg
    simpa only [d8138, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37772 (p : Pattern) (guard : d8100 p = 1) : d3552 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37590 p hg
    simpa only [d8100, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37559 p hg
    simpa only [d8100, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37773 (p : Pattern) (guard : d5854 p = 1) : d3548 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d5854, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29219 p hg
    simpa only [d5854, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37774 (p : Pattern) (guard : d8099 p = 1) : d3549 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37773 p hg
    simpa only [d8099, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29219 p hg
    simpa only [d8099, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37775 (p : Pattern) (guard : d8105 p = 1) : d3550 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37774 p hg
    simpa only [d8105, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37776 (p : Pattern) (guard : d8106 p = 1) : d3553 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37772 p hg
    simpa only [d8106, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37775 p hg
    simpa only [d8106, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37777 (p : Pattern) (guard : d8107 p = 1) : d3553 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37446 p hg
    simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37776 p hg
    simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37778 (p : Pattern) (guard : d8100 p = 1) : d3552 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37521 p hg
    simpa only [d8100, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37559 p hg
    simpa only [d8100, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37779 (p : Pattern) (guard : d8106 p = 1) : d3553 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37778 p hg
    simpa only [d8106, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37775 p hg
    simpa only [d8106, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37780 (p : Pattern) (guard : d0 p = 1) : d3557 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37781 (p : Pattern) (guard : d8105 p = 1) : d3558 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37605 p hg
    simpa only [d8105, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37780 p hg
    simpa only [d8105, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37782 (p : Pattern) (guard : d0 p = 1) : d3562 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37783 (p : Pattern) (guard : d8111 p = 1) : d3563 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37781 p hg
    simpa only [d8111, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37782 p hg
    simpa only [d8111, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37784 (p : Pattern) (guard : d8112 p = 1) : d3564 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37779 p hg
    simpa only [d8112, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37783 p hg
    simpa only [d8112, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37785 (p : Pattern) (guard : d8113 p = 1) : d3707 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37777 p hg
    simpa only [d8113, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37784 p hg
    simpa only [d8113, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37786 (p : Pattern) (guard : d8100 p = 1) : d3552 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37492 p hg
    simpa only [d8100, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37559 p hg
    simpa only [d8100, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37787 (p : Pattern) (guard : d8106 p = 1) : d3553 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37786 p hg
    simpa only [d8106, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37775 p hg
    simpa only [d8106, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37788 (p : Pattern) (guard : d8105 p = 1) : d3558 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37534 p hg
    simpa only [d8105, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37780 p hg
    simpa only [d8105, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37789 (p : Pattern) (guard : d8111 p = 1) : d3563 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37788 p hg
    simpa only [d8111, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37782 p hg
    simpa only [d8111, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37790 (p : Pattern) (guard : d8112 p = 1) : d3564 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37787 p hg
    simpa only [d8112, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37789 p hg
    simpa only [d8112, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37791 (p : Pattern) (guard : d8117 p = 1) : d3574 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36723 p hg
    simpa only [d8117, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37792 (p : Pattern) (guard : d8118 p = 1) : d3575 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37790 p hg
    simpa only [d8118, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37791 p hg
    simpa only [d8118, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37793 (p : Pattern) (guard : d8119 p = 1) : d3708 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37785 p hg
    simpa only [d8119, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37792 p hg
    simpa only [d8119, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37794 (p : Pattern) (guard : d8106 p = 1) : d3589 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36967 p hg
    simpa only [d8106, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36461 p hg
    simpa only [d8106, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37795 (p : Pattern) (guard : d8111 p = 1) : d3595 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37626 p hg
    simpa only [d8111, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36765 p hg
    simpa only [d8111, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37796 (p : Pattern) (guard : d8112 p = 1) : d3596 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37794 p hg
    simpa only [d8112, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37795 p hg
    simpa only [d8112, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37797 (p : Pattern) (guard : d8111 p = 1) : d3600 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37626 p hg
    simpa only [d8111, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36471 p hg
    simpa only [d8111, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37798 (p : Pattern) (guard : d8117 p = 1) : d3607 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37797 p hg
    simpa only [d8117, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37613 p hg
    simpa only [d8117, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37799 (p : Pattern) (guard : d8118 p = 1) : d3608 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37796 p hg
    simpa only [d8118, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37798 p hg
    simpa only [d8118, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
