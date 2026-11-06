/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons333
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46760 (p : Pattern) (guard : d8130 p = 1) : d2977 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d8130, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46745 p hg
    simpa only [d8130, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46761 (p : Pattern) (guard : d8131 p = 1) : d2978 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46754 p hg
    simpa only [d8131, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d8131, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46762 (p : Pattern) (guard : d8137 p = 1) : d2990 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2990, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d8137, d2990, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2990, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d2990, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46763 (p : Pattern) (guard : d8138 p = 1) : d2991 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2991, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46748 p hg
    simpa only [d8138, d2991, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2991, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d8138, d2991, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46764 (p : Pattern) (guard : d8139 p = 1) : d2992 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d2992, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d8139, d2992, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d2992, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d8139, d2992, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46765 (p : Pattern) (guard : d8140 p = 1) : d2992 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46541 p hg
    simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46764 p hg
    simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46766 (p : Pattern) (guard : d8086 p = 1) : d1772 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46220 p hg
    simpa only [d8086, d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38481 p hg
    simpa only [d8086, d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46767 (p : Pattern) (guard : d8087 p = 1) : d2895 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34323 p hg
    simpa only [d8087, d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46766 p hg
    simpa only [d8087, d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46768 (p : Pattern) (guard : d8092 p = 1) : d2896 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46767 p hg
    simpa only [d8092, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39004 p hg
    simpa only [d8092, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46769 (p : Pattern) (guard : d8097 p = 1) : d2896 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46768 p hg
    simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46570 p hg
    simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46770 (p : Pattern) (guard : d8102 p = 1) : d2899 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46547 p hg
    simpa only [d8102, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46575 p hg
    simpa only [d8102, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46771 (p : Pattern) (guard : d8103 p = 1) : d2900 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46769 p hg
    simpa only [d8103, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46770 p hg
    simpa only [d8103, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46772 (p : Pattern) (guard : d8107 p = 1) : d2903 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46285 p hg
    simpa only [d8107, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46773 (p : Pattern) (guard : d8108 p = 1) : d2904 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46551 p hg
    simpa only [d8108, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46772 p hg
    simpa only [d8108, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46774 (p : Pattern) (guard : d8109 p = 1) : d2905 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46771 p hg
    simpa only [d8109, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46773 p hg
    simpa only [d8109, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46775 (p : Pattern) (guard : d8091 p = 1) : d2906 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34620 p hg
    simpa only [d8091, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38498 p hg
    simpa only [d8091, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46776 (p : Pattern) (guard : d8096 p = 1) : d2907 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46775 p hg
    simpa only [d8096, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46777 (p : Pattern) (guard : d8102 p = 1) : d2909 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46776 p hg
    simpa only [d8102, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46586 p hg
    simpa only [d8102, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46778 (p : Pattern) (guard : d8101 p = 1) : d2910 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46561 p hg
    simpa only [d8101, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46779 (p : Pattern) (guard : d8107 p = 1) : d2913 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46778 p hg
    simpa only [d8107, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46437 p hg
    simpa only [d8107, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46780 (p : Pattern) (guard : d8108 p = 1) : d2914 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46777 p hg
    simpa only [d8108, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46779 p hg
    simpa only [d8108, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46781 (p : Pattern) (guard : d8101 p = 1) : d2915 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46462 p hg
    simpa only [d8101, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46782 (p : Pattern) (guard : d8107 p = 1) : d2916 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46781 p hg
    simpa only [d8107, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46437 p hg
    simpa only [d8107, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46783 (p : Pattern) (guard : d8113 p = 1) : d2919 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46782 p hg
    simpa only [d8113, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46442 p hg
    simpa only [d8113, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46784 (p : Pattern) (guard : d8114 p = 1) : d2920 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46780 p hg
    simpa only [d8114, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46783 p hg
    simpa only [d8114, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46785 (p : Pattern) (guard : d8115 p = 1) : d2921 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46774 p hg
    simpa only [d8115, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46784 p hg
    simpa only [d8115, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46786 (p : Pattern) (guard : d8085 p = 1) : d1771 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d8085, d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8085, d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46787 (p : Pattern) (guard : d8090 p = 1) : d1772 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46786 p hg
    simpa only [d8090, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38702 p hg
    simpa only [d8090, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46788 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d8091, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46787 p hg
    simpa only [d8091, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46789 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46788 p hg
    simpa only [d8096, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39026 p hg
    simpa only [d8096, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46790 (p : Pattern) (guard : d8095 p = 1) : d2922 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d8095, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46450 p hg
    simpa only [d8095, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46791 (p : Pattern) (guard : d8101 p = 1) : d2923 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46790 p hg
    simpa only [d8101, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38671 p hg
    simpa only [d8101, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46792 (p : Pattern) (guard : d8102 p = 1) : d2924 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46789 p hg
    simpa only [d8102, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46791 p hg
    simpa only [d8102, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46793 (p : Pattern) (guard : d8095 p = 1) : d2897 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34975 p hg
    simpa only [d8095, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46417 p hg
    simpa only [d8095, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46794 (p : Pattern) (guard : d8101 p = 1) : d2898 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46793 p hg
    simpa only [d8101, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46795 (p : Pattern) (guard : d8100 p = 1) : d2901 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d8100, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38557 p hg
    simpa only [d8100, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46796 (p : Pattern) (guard : d8106 p = 1) : d2902 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46795 p hg
    simpa only [d8106, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38678 p hg
    simpa only [d8106, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46797 (p : Pattern) (guard : d8107 p = 1) : d2925 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46794 p hg
    simpa only [d8107, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46796 p hg
    simpa only [d8107, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46798 (p : Pattern) (guard : d8108 p = 1) : d2926 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46792 p hg
    simpa only [d8108, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46797 p hg
    simpa only [d8108, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46799 (p : Pattern) (guard : d8100 p = 1) : d2927 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34987 p hg
    simpa only [d8100, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38563 p hg
    simpa only [d8100, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46800 (p : Pattern) (guard : d8106 p = 1) : d2928 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46799 p hg
    simpa only [d8106, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38564 p hg
    simpa only [d8106, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46801 (p : Pattern) (guard : d8107 p = 1) : d2929 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46575 p hg
    simpa only [d8107, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46800 p hg
    simpa only [d8107, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46802 (p : Pattern) (guard : d8100 p = 1) : d2930 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34993 p hg
    simpa only [d8100, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38568 p hg
    simpa only [d8100, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46803 (p : Pattern) (guard : d8106 p = 1) : d2931 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46802 p hg
    simpa only [d8106, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46804 (p : Pattern) (guard : d8112 p = 1) : d2932 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46803 p hg
    simpa only [d8112, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46805 (p : Pattern) (guard : d8113 p = 1) : d2933 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46801 p hg
    simpa only [d8113, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46804 p hg
    simpa only [d8113, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46806 (p : Pattern) (guard : d8114 p = 1) : d2934 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d8114, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46805 p hg
    simpa only [d8114, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46807 (p : Pattern) (guard : d8095 p = 1) : d2906 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34828 p hg
    simpa only [d8095, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d8095, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46808 (p : Pattern) (guard : d8101 p = 1) : d2908 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46807 p hg
    simpa only [d8101, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46809 (p : Pattern) (guard : d8106 p = 1) : d2936 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46603 p hg
    simpa only [d8106, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46810 (p : Pattern) (guard : d8107 p = 1) : d2937 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46808 p hg
    simpa only [d8107, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46809 p hg
    simpa only [d8107, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46811 (p : Pattern) (guard : d8113 p = 1) : d2939 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d8113, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46469 p hg
    simpa only [d8113, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46812 (p : Pattern) (guard : d8119 p = 1) : d2945 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46811 p hg
    simpa only [d8119, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46477 p hg
    simpa only [d8119, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46813 (p : Pattern) (guard : d8120 p = 1) : d2946 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d8120, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46812 p hg
    simpa only [d8120, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46814 (p : Pattern) (guard : d8121 p = 1) : d2947 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46785 p hg
    simpa only [d8121, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46813 p hg
    simpa only [d8121, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46815 (p : Pattern) (guard : d8127 p = 1) : d2979 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46814 p hg
    simpa only [d8127, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46635 p hg
    simpa only [d8127, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46816 (p : Pattern) (guard : d8091 p = 1) : d2948 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34750 p hg
    simpa only [d8091, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46482 p hg
    simpa only [d8091, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46817 (p : Pattern) (guard : d8096 p = 1) : d2949 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46816 p hg
    simpa only [d8096, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39055 p hg
    simpa only [d8096, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46818 (p : Pattern) (guard : d8102 p = 1) : d2952 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46817 p hg
    simpa only [d8102, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46625 p hg
    simpa only [d8102, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46819 (p : Pattern) (guard : d8101 p = 1) : d2953 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46807 p hg
    simpa only [d8101, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46820 (p : Pattern) (guard : d8107 p = 1) : d2955 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46819 p hg
    simpa only [d8107, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46630 p hg
    simpa only [d8107, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46821 (p : Pattern) (guard : d8108 p = 1) : d2956 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46818 p hg
    simpa only [d8108, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46820 p hg
    simpa only [d8108, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46822 (p : Pattern) (guard : d8113 p = 1) : d2959 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46615 p hg
    simpa only [d8113, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46494 p hg
    simpa only [d8113, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46823 (p : Pattern) (guard : d8114 p = 1) : d2960 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46821 p hg
    simpa only [d8114, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46822 p hg
    simpa only [d8114, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46824 (p : Pattern) (guard : d8107 p = 1) : d2964 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46350 p hg
    simpa only [d8107, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46500 p hg
    simpa only [d8107, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46825 (p : Pattern) (guard : d8113 p = 1) : d2965 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46824 p hg
    simpa only [d8113, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46826 (p : Pattern) (guard : d8119 p = 1) : d2966 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46825 p hg
    simpa only [d8119, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46827 (p : Pattern) (guard : d8120 p = 1) : d2967 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46823 p hg
    simpa only [d8120, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46826 p hg
    simpa only [d8120, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46828 (p : Pattern) (guard : d8095 p = 1) : d2950 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d8095, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46486 p hg
    simpa only [d8095, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46829 (p : Pattern) (guard : d8101 p = 1) : d2951 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46828 p hg
    simpa only [d8101, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46830 (p : Pattern) (guard : d8100 p = 1) : d2935 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34882 p hg
    simpa only [d8100, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38741 p hg
    simpa only [d8100, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46831 (p : Pattern) (guard : d8106 p = 1) : d2961 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46830 p hg
    simpa only [d8106, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46832 (p : Pattern) (guard : d8107 p = 1) : d2968 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46829 p hg
    simpa only [d8107, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46831 p hg
    simpa only [d8107, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46833 (p : Pattern) (guard : d8100 p = 1) : d2911 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d8100, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38720 p hg
    simpa only [d8100, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46834 (p : Pattern) (guard : d8106 p = 1) : d2954 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46833 p hg
    simpa only [d8106, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38721 p hg
    simpa only [d8106, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46835 (p : Pattern) (guard : d8112 p = 1) : d2969 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46834 p hg
    simpa only [d8112, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46509 p hg
    simpa only [d8112, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46836 (p : Pattern) (guard : d8113 p = 1) : d2970 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46832 p hg
    simpa only [d8113, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46835 p hg
    simpa only [d8113, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46837 (p : Pattern) (guard : d8112 p = 1) : d2971 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46630 p hg
    simpa only [d8112, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46512 p hg
    simpa only [d8112, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46838 (p : Pattern) (guard : d8118 p = 1) : d2972 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46837 p hg
    simpa only [d8118, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46839 (p : Pattern) (guard : d8119 p = 1) : d2973 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46836 p hg
    simpa only [d8119, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46838 p hg
    simpa only [d8119, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46840 (p : Pattern) (guard : d8125 p = 1) : d2977 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46839 p hg
    simpa only [d8125, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46520 p hg
    simpa only [d8125, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46841 (p : Pattern) (guard : d8126 p = 1) : d2978 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46827 p hg
    simpa only [d8126, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46840 p hg
    simpa only [d8126, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46842 (p : Pattern) (guard : d8101 p = 1) : d2957 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46284 p hg
    simpa only [d8101, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38516 p hg
    simpa only [d8101, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46843 (p : Pattern) (guard : d8107 p = 1) : d2980 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46842 p hg
    simpa only [d8107, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46359 p hg
    simpa only [d8107, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46844 (p : Pattern) (guard : d8113 p = 1) : d2981 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46843 p hg
    simpa only [d8113, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46845 (p : Pattern) (guard : d8119 p = 1) : d2983 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46844 p hg
    simpa only [d8119, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46639 p hg
    simpa only [d8119, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46846 (p : Pattern) (guard : d8125 p = 1) : d2985 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46845 p hg
    simpa only [d8125, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46641 p hg
    simpa only [d8125, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46847 (p : Pattern) (guard : d8118 p = 1) : d2982 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46804 p hg
    simpa only [d8118, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46848 (p : Pattern) (guard : d8124 p = 1) : d2984 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46847 p hg
    simpa only [d8124, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46849 (p : Pattern) (guard : d8130 p = 1) : d2986 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46848 p hg
    simpa only [d8130, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46850 (p : Pattern) (guard : d8131 p = 1) : d2987 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46846 p hg
    simpa only [d8131, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46849 p hg
    simpa only [d8131, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46851 (p : Pattern) (guard : d8132 p = 1) : d2988 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46841 p hg
    simpa only [d8132, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46850 p hg
    simpa only [d8132, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46852 (p : Pattern) (guard : d8133 p = 1) : d2989 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46815 p hg
    simpa only [d8133, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46851 p hg
    simpa only [d8133, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46853 (p : Pattern) (guard : d8102 p = 1) : d2896 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46570 p hg
    simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46682 p hg
    simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46854 (p : Pattern) (guard : d8107 p = 1) : d2899 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d8107, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46689 p hg
    simpa only [d8107, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46855 (p : Pattern) (guard : d8108 p = 1) : d2900 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46853 p hg
    simpa only [d8108, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46854 p hg
    simpa only [d8108, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46856 (p : Pattern) (guard : d8113 p = 1) : d2904 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46656 p hg
    simpa only [d8113, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46663 p hg
    simpa only [d8113, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46857 (p : Pattern) (guard : d8114 p = 1) : d2905 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46855 p hg
    simpa only [d8114, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46856 p hg
    simpa only [d8114, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46858 (p : Pattern) (guard : d8101 p = 1) : d2907 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46585 p hg
    simpa only [d8101, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46859 (p : Pattern) (guard : d8107 p = 1) : d2909 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46858 p hg
    simpa only [d8107, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46668 p hg
    simpa only [d8107, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46860 (p : Pattern) (guard : d8113 p = 1) : d2914 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46859 p hg
    simpa only [d8113, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46673 p hg
    simpa only [d8113, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46861 (p : Pattern) (guard : d8119 p = 1) : d2920 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46860 p hg
    simpa only [d8119, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46678 p hg
    simpa only [d8119, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46862 (p : Pattern) (guard : d8120 p = 1) : d2921 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46857 p hg
    simpa only [d8120, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46861 p hg
    simpa only [d8120, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46863 (p : Pattern) (guard : d8095 p = 1) : d2895 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d8095, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38945 p hg
    simpa only [d8095, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46864 (p : Pattern) (guard : d8101 p = 1) : d2896 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46863 p hg
    simpa only [d8101, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46865 (p : Pattern) (guard : d8100 p = 1) : d2922 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35045 p hg
    simpa only [d8100, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46684 p hg
    simpa only [d8100, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46866 (p : Pattern) (guard : d8106 p = 1) : d2923 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46865 p hg
    simpa only [d8106, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d8106, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46867 (p : Pattern) (guard : d8107 p = 1) : d2924 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46864 p hg
    simpa only [d8107, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46866 p hg
    simpa only [d8107, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46868 (p : Pattern) (guard : d8100 p = 1) : d2897 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35051 p hg
    simpa only [d8100, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d8100, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46869 (p : Pattern) (guard : d8106 p = 1) : d2898 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46868 p hg
    simpa only [d8106, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46870 (p : Pattern) (guard : d8112 p = 1) : d2925 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46869 p hg
    simpa only [d8112, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46690 p hg
    simpa only [d8112, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46871 (p : Pattern) (guard : d8113 p = 1) : d2926 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46867 p hg
    simpa only [d8113, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46870 p hg
    simpa only [d8113, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46872 (p : Pattern) (guard : d8112 p = 1) : d2929 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46689 p hg
    simpa only [d8112, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46512 p hg
    simpa only [d8112, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46873 (p : Pattern) (guard : d8118 p = 1) : d2933 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46872 p hg
    simpa only [d8118, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46874 (p : Pattern) (guard : d8119 p = 1) : d2934 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46871 p hg
    simpa only [d8119, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46873 p hg
    simpa only [d8119, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46875 (p : Pattern) (guard : d8100 p = 1) : d2906 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34925 p hg
    simpa only [d8100, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38955 p hg
    simpa only [d8100, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46876 (p : Pattern) (guard : d8106 p = 1) : d2908 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46875 p hg
    simpa only [d8106, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46877 (p : Pattern) (guard : d8112 p = 1) : d2937 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46876 p hg
    simpa only [d8112, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46697 p hg
    simpa only [d8112, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46878 (p : Pattern) (guard : d8118 p = 1) : d2939 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46877 p hg
    simpa only [d8118, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46700 p hg
    simpa only [d8118, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46879 (p : Pattern) (guard : d8124 p = 1) : d2945 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46878 p hg
    simpa only [d8124, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d8124, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46880 (p : Pattern) (guard : d8125 p = 1) : d2946 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46874 p hg
    simpa only [d8125, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46879 p hg
    simpa only [d8125, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46881 (p : Pattern) (guard : d8126 p = 1) : d2947 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46862 p hg
    simpa only [d8126, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46880 p hg
    simpa only [d8126, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46882 (p : Pattern) (guard : d8132 p = 1) : d2979 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46881 p hg
    simpa only [d8132, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d8132, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46883 (p : Pattern) (guard : d8095 p = 1) : d2948 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34845 p hg
    simpa only [d8095, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d8095, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46884 (p : Pattern) (guard : d8101 p = 1) : d2949 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46883 p hg
    simpa only [d8101, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46885 (p : Pattern) (guard : d8107 p = 1) : d2952 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46884 p hg
    simpa only [d8107, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46756 p hg
    simpa only [d8107, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46886 (p : Pattern) (guard : d8106 p = 1) : d2953 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46875 p hg
    simpa only [d8106, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46887 (p : Pattern) (guard : d8112 p = 1) : d2955 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46886 p hg
    simpa only [d8112, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d8112, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46888 (p : Pattern) (guard : d8113 p = 1) : d2956 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46885 p hg
    simpa only [d8113, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46887 p hg
    simpa only [d8113, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46889 (p : Pattern) (guard : d8119 p = 1) : d2960 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46888 p hg
    simpa only [d8119, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46723 p hg
    simpa only [d8119, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46890 (p : Pattern) (guard : d8125 p = 1) : d2967 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46889 p hg
    simpa only [d8125, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d8125, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46891 (p : Pattern) (guard : d8100 p = 1) : d2950 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35446 p hg
    simpa only [d8100, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d8100, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46892 (p : Pattern) (guard : d8106 p = 1) : d2951 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46891 p hg
    simpa only [d8106, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46893 (p : Pattern) (guard : d8112 p = 1) : d2968 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46892 p hg
    simpa only [d8112, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46733 p hg
    simpa only [d8112, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46894 (p : Pattern) (guard : d8118 p = 1) : d2970 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46893 p hg
    simpa only [d8118, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46736 p hg
    simpa only [d8118, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46895 (p : Pattern) (guard : d8124 p = 1) : d2973 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46894 p hg
    simpa only [d8124, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d8124, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46896 (p : Pattern) (guard : d8130 p = 1) : d2977 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46895 p hg
    simpa only [d8130, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46745 p hg
    simpa only [d8130, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46897 (p : Pattern) (guard : d8131 p = 1) : d2978 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46890 p hg
    simpa only [d8131, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46896 p hg
    simpa only [d8131, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46898 (p : Pattern) (guard : d8137 p = 1) : d2990 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46897 p hg
    simpa only [d8137, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46899 (p : Pattern) (guard : d8138 p = 1) : d2991 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46882 p hg
    simpa only [d8138, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46898 p hg
    simpa only [d8138, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
