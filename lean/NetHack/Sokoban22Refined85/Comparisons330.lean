/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons329
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46200 (p : Pattern) (guard : d8136 p = 1) : d774 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d774, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46198 p hg
    simpa only [d8136, d774, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d774, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46199 p hg
    simpa only [d8136, d774, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46201 (p : Pattern) (guard : d8142 p = 1) : d775 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d775, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46200 p hg
    simpa only [d8142, d775, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d775, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38307 p hg
    simpa only [d8142, d775, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46202 (p : Pattern) (guard : d8143 p = 1) : d776 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d776, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46197 p hg
    simpa only [d8143, d776, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d776, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46201 p hg
    simpa only [d8143, d776, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46203 (p : Pattern) (guard : d8129 p = 1) : d405 p ≤ (0 : Int) + d405 p := by
  omega
theorem compare46204 (p : Pattern) (guard : d8130 p = 1) : d753 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d753, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35826 p hg
    simpa only [d8130, d753, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d753, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46203 p hg
    simpa only [d8130, d753, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46205 (p : Pattern) (guard : d8135 p = 1) : d771 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d771, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35843 p hg
    simpa only [d8135, d771, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d771, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d771, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46206 (p : Pattern) (guard : d8136 p = 1) : d777 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d777, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46204 p hg
    simpa only [d8136, d777, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d777, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46205 p hg
    simpa only [d8136, d777, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46207 (p : Pattern) (guard : d8135 p = 1) : d778 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d778, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41523 p hg
    simpa only [d8135, d778, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d778, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d778, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46208 (p : Pattern) (guard : d0 p = 1) : d779 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46209 (p : Pattern) (guard : d8141 p = 1) : d780 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d780, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46207 p hg
    simpa only [d8141, d780, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d780, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46208 p hg
    simpa only [d8141, d780, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46210 (p : Pattern) (guard : d8142 p = 1) : d781 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d781, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46206 p hg
    simpa only [d8142, d781, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d781, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46209 p hg
    simpa only [d8142, d781, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46211 (p : Pattern) (guard : d8135 p = 1) : d782 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d782, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41530 p hg
    simpa only [d8135, d782, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d782, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d782, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46212 (p : Pattern) (guard : d0 p = 1) : d779 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46213 (p : Pattern) (guard : d8141 p = 1) : d783 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d783, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46211 p hg
    simpa only [d8141, d783, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d783, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46212 p hg
    simpa only [d8141, d783, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46214 (p : Pattern) (guard : d8147 p = 1) : d784 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d784, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46213 p hg
    simpa only [d8147, d784, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d784, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d784, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46215 (p : Pattern) (guard : d8148 p = 1) : d785 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d785, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46210 p hg
    simpa only [d8148, d785, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d785, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46214 p hg
    simpa only [d8148, d785, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46216 (p : Pattern) (guard : d8149 p = 1) : d786 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d786, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46202 p hg
    simpa only [d8149, d786, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d786, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46215 p hg
    simpa only [d8149, d786, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46217 (p : Pattern) (guard : d8150 p = 1) : d787 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d787, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46189 p hg
    simpa only [d8150, d787, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d787, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46216 p hg
    simpa only [d8150, d787, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46218 (p : Pattern) (guard : d8151 p = 1) : d788 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46165 p hg
    simpa only [d8151, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46217 p hg
    simpa only [d8151, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46219 (p : Pattern) (guard : d8152 p = 1) : d789 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46137 p hg
    simpa only [d8152, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46218 p hg
    simpa only [d8152, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46220 (p : Pattern) (guard : d1 p = 1) : d1771 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d1771, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d1771, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46221 (p : Pattern) (guard : d1 p = 1) : d1772 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46220 p hg
    simpa only [d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46222 (p : Pattern) (guard : d1 p = 1) : d2895 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34323 p hg
    simpa only [d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46221 p hg
    simpa only [d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46223 (p : Pattern) (guard : d8088 p = 1) : d2896 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46222 p hg
    simpa only [d8088, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38340 p hg
    simpa only [d8088, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46224 (p : Pattern) (guard : d8087 p = 1) : d2895 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34336 p hg
    simpa only [d8087, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38581 p hg
    simpa only [d8087, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46225 (p : Pattern) (guard : d8092 p = 1) : d2896 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46224 p hg
    simpa only [d8092, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38348 p hg
    simpa only [d8092, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46226 (p : Pattern) (guard : d8093 p = 1) : d2896 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46223 p hg
    simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46225 p hg
    simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46227 (p : Pattern) (guard : d8087 p = 1) : d2895 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34350 p hg
    simpa only [d8087, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38482 p hg
    simpa only [d8087, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46228 (p : Pattern) (guard : d8092 p = 1) : d2896 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46227 p hg
    simpa only [d8092, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38354 p hg
    simpa only [d8092, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46229 (p : Pattern) (guard : d8085 p = 1) : d2011 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d8085, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41808 p hg
    simpa only [d8085, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46230 (p : Pattern) (guard : d8089 p = 1) : d1795 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41808 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38505 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46231 (p : Pattern) (guard : d8090 p = 1) : d2012 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46229 p hg
    simpa only [d8090, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46230 p hg
    simpa only [d8090, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46232 (p : Pattern) (guard : d8091 p = 1) : d2897 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34361 p hg
    simpa only [d8091, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46231 p hg
    simpa only [d8091, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46233 (p : Pattern) (guard : d8096 p = 1) : d2898 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46232 p hg
    simpa only [d8096, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38364 p hg
    simpa only [d8096, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46234 (p : Pattern) (guard : d8097 p = 1) : d2899 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46228 p hg
    simpa only [d8097, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46233 p hg
    simpa only [d8097, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46235 (p : Pattern) (guard : d8098 p = 1) : d2900 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46226 p hg
    simpa only [d8098, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46234 p hg
    simpa only [d8098, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46236 (p : Pattern) (guard : d8087 p = 1) : d2895 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34374 p hg
    simpa only [d8087, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38482 p hg
    simpa only [d8087, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46237 (p : Pattern) (guard : d8092 p = 1) : d2896 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46236 p hg
    simpa only [d8092, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38371 p hg
    simpa only [d8092, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46238 (p : Pattern) (guard : d8091 p = 1) : d2897 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34382 p hg
    simpa only [d8091, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46231 p hg
    simpa only [d8091, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46239 (p : Pattern) (guard : d8096 p = 1) : d2898 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46238 p hg
    simpa only [d8096, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38364 p hg
    simpa only [d8096, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46240 (p : Pattern) (guard : d8097 p = 1) : d2899 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46237 p hg
    simpa only [d8097, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46239 p hg
    simpa only [d8097, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46241 (p : Pattern) (guard : d8091 p = 1) : d2901 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34391 p hg
    simpa only [d8091, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38614 p hg
    simpa only [d8091, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46242 (p : Pattern) (guard : d8096 p = 1) : d2902 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46241 p hg
    simpa only [d8096, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38384 p hg
    simpa only [d8096, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46243 (p : Pattern) (guard : d8102 p = 1) : d2903 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46242 p hg
    simpa only [d8102, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46244 (p : Pattern) (guard : d8103 p = 1) : d2904 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46240 p hg
    simpa only [d8103, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46243 p hg
    simpa only [d8103, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46245 (p : Pattern) (guard : d8104 p = 1) : d2905 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46235 p hg
    simpa only [d8104, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46244 p hg
    simpa only [d8104, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46246 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38485 p hg
    simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46247 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46246 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46248 (p : Pattern) (guard : d1 p = 1) : d1785 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46249 (p : Pattern) (guard : d8084 p = 1) : d1786 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46248 p hg
    simpa only [d8084, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d8084, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46250 (p : Pattern) (guard : d8085 p = 1) : d1787 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d8085, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46249 p hg
    simpa only [d8085, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46251 (p : Pattern) (guard : d8086 p = 1) : d1788 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46247 p hg
    simpa only [d8086, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46250 p hg
    simpa only [d8086, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46252 (p : Pattern) (guard : d8087 p = 1) : d2906 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34405 p hg
    simpa only [d8087, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46251 p hg
    simpa only [d8087, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46253 (p : Pattern) (guard : d8092 p = 1) : d2907 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46252 p hg
    simpa only [d8092, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38397 p hg
    simpa only [d8092, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46254 (p : Pattern) (guard : d8091 p = 1) : d2906 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34415 p hg
    simpa only [d8091, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38498 p hg
    simpa only [d8091, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46255 (p : Pattern) (guard : d8096 p = 1) : d2908 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46254 p hg
    simpa only [d8096, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38404 p hg
    simpa only [d8096, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46256 (p : Pattern) (guard : d8097 p = 1) : d2909 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46253 p hg
    simpa only [d8097, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46255 p hg
    simpa only [d8097, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46257 (p : Pattern) (guard : d8091 p = 1) : d2906 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34343 p hg
    simpa only [d8091, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38498 p hg
    simpa only [d8091, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46258 (p : Pattern) (guard : d8096 p = 1) : d2910 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46257 p hg
    simpa only [d8096, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38409 p hg
    simpa only [d8096, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46259 (p : Pattern) (guard : d8095 p = 1) : d2911 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34365 p hg
    simpa only [d8095, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38507 p hg
    simpa only [d8095, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46260 (p : Pattern) (guard : d8101 p = 1) : d2912 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46259 p hg
    simpa only [d8101, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46261 (p : Pattern) (guard : d8102 p = 1) : d2913 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46258 p hg
    simpa only [d8102, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46260 p hg
    simpa only [d8102, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46262 (p : Pattern) (guard : d8103 p = 1) : d2914 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46256 p hg
    simpa only [d8103, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46261 p hg
    simpa only [d8103, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46263 (p : Pattern) (guard : d8091 p = 1) : d2906 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34341 p hg
    simpa only [d8091, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38498 p hg
    simpa only [d8091, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46264 (p : Pattern) (guard : d8096 p = 1) : d2915 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46263 p hg
    simpa only [d8096, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46265 (p : Pattern) (guard : d8102 p = 1) : d2916 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46264 p hg
    simpa only [d8102, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46260 p hg
    simpa only [d8102, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46266 (p : Pattern) (guard : d8095 p = 1) : d2901 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34395 p hg
    simpa only [d8095, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38515 p hg
    simpa only [d8095, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46267 (p : Pattern) (guard : d8101 p = 1) : d2917 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46266 p hg
    simpa only [d8101, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46268 (p : Pattern) (guard : d8107 p = 1) : d2918 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46267 p hg
    simpa only [d8107, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46269 (p : Pattern) (guard : d8108 p = 1) : d2919 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46265 p hg
    simpa only [d8108, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46268 p hg
    simpa only [d8108, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46270 (p : Pattern) (guard : d8109 p = 1) : d2920 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46262 p hg
    simpa only [d8109, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46269 p hg
    simpa only [d8109, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46271 (p : Pattern) (guard : d8110 p = 1) : d2921 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46245 p hg
    simpa only [d8110, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46270 p hg
    simpa only [d8110, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46272 (p : Pattern) (guard : d1 p = 1) : d1771 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46273 (p : Pattern) (guard : d8086 p = 1) : d1772 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46272 p hg
    simpa only [d8086, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38481 p hg
    simpa only [d8086, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46274 (p : Pattern) (guard : d8087 p = 1) : d2895 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34463 p hg
    simpa only [d8087, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46273 p hg
    simpa only [d8087, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46275 (p : Pattern) (guard : d8092 p = 1) : d2896 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46274 p hg
    simpa only [d8092, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38425 p hg
    simpa only [d8092, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46276 (p : Pattern) (guard : d8085 p = 1) : d2029 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d8085, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38524 p hg
    simpa only [d8085, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46277 (p : Pattern) (guard : d8089 p = 1) : d1714 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38524 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38548 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46278 (p : Pattern) (guard : d8090 p = 1) : d2030 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46276 p hg
    simpa only [d8090, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46277 p hg
    simpa only [d8090, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46279 (p : Pattern) (guard : d8091 p = 1) : d2922 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34470 p hg
    simpa only [d8091, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46278 p hg
    simpa only [d8091, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46280 (p : Pattern) (guard : d8096 p = 1) : d2923 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46279 p hg
    simpa only [d8096, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38435 p hg
    simpa only [d8096, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46281 (p : Pattern) (guard : d8097 p = 1) : d2924 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46275 p hg
    simpa only [d8097, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46280 p hg
    simpa only [d8097, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46282 (p : Pattern) (guard : d8091 p = 1) : d2897 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34482 p hg
    simpa only [d8091, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46231 p hg
    simpa only [d8091, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46283 (p : Pattern) (guard : d8096 p = 1) : d2898 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46282 p hg
    simpa only [d8096, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38364 p hg
    simpa only [d8096, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46284 (p : Pattern) (guard : d8095 p = 1) : d2901 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34486 p hg
    simpa only [d8095, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38515 p hg
    simpa only [d8095, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46285 (p : Pattern) (guard : d8101 p = 1) : d2902 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46284 p hg
    simpa only [d8101, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38444 p hg
    simpa only [d8101, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46286 (p : Pattern) (guard : d8102 p = 1) : d2925 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46283 p hg
    simpa only [d8102, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46285 p hg
    simpa only [d8102, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46287 (p : Pattern) (guard : d8103 p = 1) : d2926 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46281 p hg
    simpa only [d8103, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46286 p hg
    simpa only [d8103, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46288 (p : Pattern) (guard : d8095 p = 1) : d2927 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34500 p hg
    simpa only [d8095, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38450 p hg
    simpa only [d8095, d2927, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46289 (p : Pattern) (guard : d8101 p = 1) : d2928 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46288 p hg
    simpa only [d8101, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38451 p hg
    simpa only [d8101, d2928, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46290 (p : Pattern) (guard : d8102 p = 1) : d2929 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46233 p hg
    simpa only [d8102, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46289 p hg
    simpa only [d8102, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46291 (p : Pattern) (guard : d8095 p = 1) : d2930 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34509 p hg
    simpa only [d8095, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38456 p hg
    simpa only [d8095, d2930, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46292 (p : Pattern) (guard : d8101 p = 1) : d2931 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46291 p hg
    simpa only [d8101, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d2931, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46293 (p : Pattern) (guard : d8107 p = 1) : d2932 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46292 p hg
    simpa only [d8107, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46294 (p : Pattern) (guard : d8108 p = 1) : d2933 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46290 p hg
    simpa only [d8108, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46293 p hg
    simpa only [d8108, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46295 (p : Pattern) (guard : d8109 p = 1) : d2934 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46287 p hg
    simpa only [d8109, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46294 p hg
    simpa only [d8109, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46296 (p : Pattern) (guard : d8091 p = 1) : d2906 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34518 p hg
    simpa only [d8091, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38498 p hg
    simpa only [d8091, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46297 (p : Pattern) (guard : d8096 p = 1) : d2908 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46296 p hg
    simpa only [d8096, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38404 p hg
    simpa only [d8096, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46298 (p : Pattern) (guard : d8095 p = 1) : d2935 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34524 p hg
    simpa only [d8095, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38550 p hg
    simpa only [d8095, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46299 (p : Pattern) (guard : d8101 p = 1) : d2936 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46298 p hg
    simpa only [d8101, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46300 (p : Pattern) (guard : d8102 p = 1) : d2937 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46297 p hg
    simpa only [d8102, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46299 p hg
    simpa only [d8102, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46301 (p : Pattern) (guard : d8100 p = 1) : d2901 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34452 p hg
    simpa only [d8100, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38557 p hg
    simpa only [d8100, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46302 (p : Pattern) (guard : d8106 p = 1) : d2917 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46301 p hg
    simpa only [d8106, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46303 (p : Pattern) (guard : d8107 p = 1) : d2938 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46260 p hg
    simpa only [d8107, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46302 p hg
    simpa only [d8107, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46304 (p : Pattern) (guard : d8108 p = 1) : d2939 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46300 p hg
    simpa only [d8108, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46303 p hg
    simpa only [d8108, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46305 (p : Pattern) (guard : d8100 p = 1) : d2927 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34502 p hg
    simpa only [d8100, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38563 p hg
    simpa only [d8100, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46306 (p : Pattern) (guard : d8106 p = 1) : d2940 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46305 p hg
    simpa only [d8106, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46307 (p : Pattern) (guard : d8107 p = 1) : d2941 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46260 p hg
    simpa only [d8107, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46306 p hg
    simpa only [d8107, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46308 (p : Pattern) (guard : d8100 p = 1) : d2930 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34511 p hg
    simpa only [d8100, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38568 p hg
    simpa only [d8100, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46309 (p : Pattern) (guard : d8106 p = 1) : d2942 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46308 p hg
    simpa only [d8106, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46310 (p : Pattern) (guard : d8112 p = 1) : d2943 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46309 p hg
    simpa only [d8112, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46311 (p : Pattern) (guard : d8113 p = 1) : d2944 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46307 p hg
    simpa only [d8113, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46310 p hg
    simpa only [d8113, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46312 (p : Pattern) (guard : d8114 p = 1) : d2945 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46304 p hg
    simpa only [d8114, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46311 p hg
    simpa only [d8114, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46313 (p : Pattern) (guard : d8115 p = 1) : d2946 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46295 p hg
    simpa only [d8115, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46312 p hg
    simpa only [d8115, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46314 (p : Pattern) (guard : d8116 p = 1) : d2947 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46271 p hg
    simpa only [d8116, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46313 p hg
    simpa only [d8116, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46315 (p : Pattern) (guard : d8085 p = 1) : d2047 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d8085, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38486 p hg
    simpa only [d8085, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46316 (p : Pattern) (guard : d8086 p = 1) : d2048 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46247 p hg
    simpa only [d8086, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46315 p hg
    simpa only [d8086, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46317 (p : Pattern) (guard : d8087 p = 1) : d2948 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34374 p hg
    simpa only [d8087, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46316 p hg
    simpa only [d8087, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46318 (p : Pattern) (guard : d8092 p = 1) : d2949 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46317 p hg
    simpa only [d8092, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38483 p hg
    simpa only [d8092, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46319 (p : Pattern) (guard : d5843 p = 1) : d2051 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46320 (p : Pattern) (guard : d5847 p = 1) : d2052 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46319 p hg
    simpa only [d5847, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46321 (p : Pattern) (guard : d8089 p = 1) : d2053 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8089, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46320 p hg
    simpa only [d8089, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46322 (p : Pattern) (guard : d8090 p = 1) : d2054 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38487 p hg
    simpa only [d8090, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46321 p hg
    simpa only [d8090, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46323 (p : Pattern) (guard : d8091 p = 1) : d2950 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34518 p hg
    simpa only [d8091, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46322 p hg
    simpa only [d8091, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46324 (p : Pattern) (guard : d8096 p = 1) : d2951 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46323 p hg
    simpa only [d8096, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38492 p hg
    simpa only [d8096, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46325 (p : Pattern) (guard : d8097 p = 1) : d2952 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46318 p hg
    simpa only [d8097, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46324 p hg
    simpa only [d8097, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46326 (p : Pattern) (guard : d8096 p = 1) : d2953 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46254 p hg
    simpa only [d8096, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38499 p hg
    simpa only [d8096, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46327 (p : Pattern) (guard : d8101 p = 1) : d2954 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46259 p hg
    simpa only [d8101, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38508 p hg
    simpa only [d8101, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46328 (p : Pattern) (guard : d8102 p = 1) : d2955 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46326 p hg
    simpa only [d8102, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46327 p hg
    simpa only [d8102, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46329 (p : Pattern) (guard : d8103 p = 1) : d2956 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46325 p hg
    simpa only [d8103, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46328 p hg
    simpa only [d8103, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46330 (p : Pattern) (guard : d8096 p = 1) : d2953 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46257 p hg
    simpa only [d8096, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38499 p hg
    simpa only [d8096, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46331 (p : Pattern) (guard : d8102 p = 1) : d2955 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46330 p hg
    simpa only [d8102, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46327 p hg
    simpa only [d8102, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46332 (p : Pattern) (guard : d8101 p = 1) : d2957 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46266 p hg
    simpa only [d8101, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38516 p hg
    simpa only [d8101, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46333 (p : Pattern) (guard : d8107 p = 1) : d2958 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46332 p hg
    simpa only [d8107, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46334 (p : Pattern) (guard : d8108 p = 1) : d2959 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46331 p hg
    simpa only [d8108, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46333 p hg
    simpa only [d8108, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46335 (p : Pattern) (guard : d8109 p = 1) : d2960 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46329 p hg
    simpa only [d8109, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46334 p hg
    simpa only [d8109, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46336 (p : Pattern) (guard : d8091 p = 1) : d2935 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34564 p hg
    simpa only [d8091, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38526 p hg
    simpa only [d8091, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46337 (p : Pattern) (guard : d8096 p = 1) : d2961 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46336 p hg
    simpa only [d8096, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46338 (p : Pattern) (guard : d8095 p = 1) : d2962 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34426 p hg
    simpa only [d8095, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38533 p hg
    simpa only [d8095, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46339 (p : Pattern) (guard : d8101 p = 1) : d2963 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46338 p hg
    simpa only [d8101, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
