/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons143
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20160 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20161 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d102 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20154 p hg
    simpa only [d5849, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20160 p hg
    simpa only [d5849, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20162 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20161 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20145 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20163 (p : Pattern) (guard : d5849 p = 1) : d2327 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20162 p hg
    simpa only [d2327, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20152 p hg
    simpa only [d2327, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20164 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20165 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20166 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  omega
theorem compare20167 (p : Pattern) (guard : d5843 p = 1) : d107 p ≤ (0 : Int) + d106 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20166 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20168 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d106 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14656 p hg
    simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20169 (p : Pattern) (guard : d5848 p = 1) : d107 p ≤ (0 : Int) + d106 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20168 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20170 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20171 (p : Pattern) (guard : d5849 p = 1) : d2328 p ≤ (0 : Int) + d106 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20169 p hg
    simpa only [d5849, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5849, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20172 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20173 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d3748 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d3748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d107, d3748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d3748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20172 p hg
    simpa only [d5847, d107, d3748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20174 (p : Pattern) (guard : d5848 p = 1) : d107 p ≤ (0 : Int) + d3749 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d5848, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20173 p hg
    simpa only [d5848, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20175 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3748 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20176 (p : Pattern) (guard : d5849 p = 1) : d2328 p ≤ (0 : Int) + d3750 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2328, d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20174 p hg
    simpa only [d5849, d2328, d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2328, d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20175 p hg
    simpa only [d5849, d2328, d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20177 (p : Pattern) (guard : d5849 p = 1) : d2328 p ≤ (0 : Int) + d3751 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20171 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20176 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20178 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20179 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d3752 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d3752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d107, d3752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d3752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20178 p hg
    simpa only [d5847, d107, d3752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20180 (p : Pattern) (guard : d5848 p = 1) : d107 p ≤ (0 : Int) + d3753 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d5848, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20179 p hg
    simpa only [d5848, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20181 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3752 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20182 (p : Pattern) (guard : d5849 p = 1) : d2328 p ≤ (0 : Int) + d3754 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2328, d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20180 p hg
    simpa only [d5849, d2328, d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2328, d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20181 p hg
    simpa only [d5849, d2328, d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20183 (p : Pattern) (guard : d5849 p = 1) : d2329 p ≤ (0 : Int) + d3755 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2329, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20182 p hg
    simpa only [d2329, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2329, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2329, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20184 (p : Pattern) (guard : d5849 p = 1) : d2330 p ≤ (0 : Int) + d3756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2330, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20177 p hg
    simpa only [d2330, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2330, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20183 p hg
    simpa only [d2330, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20185 (p : Pattern) (guard : d5849 p = 1) : d2331 p ≤ (0 : Int) + d3757 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2331, d3757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20163 p hg
    simpa only [d2331, d3757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2331, d3757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20184 p hg
    simpa only [d2331, d3757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20186 (p : Pattern) (guard : d5849 p = 1) : d2332 p ≤ (0 : Int) + d3758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2332, d3758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20159 p hg
    simpa only [d2332, d3758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2332, d3758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20185 p hg
    simpa only [d2332, d3758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20187 (p : Pattern) (guard : d5849 p = 1) : d2333 p ≤ (0 : Int) + d3759 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2333, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20003 p hg
    simpa only [d2333, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2333, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2333, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20188 (p : Pattern) (guard : d5849 p = 1) : d2334 p ≤ (0 : Int) + d3760 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2334, d3760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20185 p hg
    simpa only [d2334, d3760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2334, d3760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20187 p hg
    simpa only [d2334, d3760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20189 (p : Pattern) (guard : d5849 p = 1) : d2335 p ≤ (0 : Int) + d3761 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2335, d3761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20186 p hg
    simpa only [d2335, d3761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2335, d3761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20188 p hg
    simpa only [d2335, d3761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20190 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20191 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d3762 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d103, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20190 p hg
    simpa only [d5847, d103, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20192 (p : Pattern) (guard : d5848 p = 1) : d103 p ≤ (0 : Int) + d3763 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5848, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20191 p hg
    simpa only [d5848, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20193 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20194 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3765 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2319, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20192 p hg
    simpa only [d5849, d2319, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2319, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20193 p hg
    simpa only [d5849, d2319, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20195 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3766 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20161 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20194 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20196 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20197 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20198 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d115 p := by
  omega
theorem compare20199 (p : Pattern) (guard : d5843 p = 1) : d116 p ≤ (0 : Int) + d115 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20198 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20200 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20201 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d3767 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d116, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20200 p hg
    simpa only [d5847, d116, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20202 (p : Pattern) (guard : d5848 p = 1) : d116 p ≤ (0 : Int) + d3768 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d5848, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20201 p hg
    simpa only [d5848, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20203 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20204 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d3771 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2336, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20202 p hg
    simpa only [d5849, d2336, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2336, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20203 p hg
    simpa only [d5849, d2336, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20205 (p : Pattern) (guard : d5849 p = 1) : d2337 p ≤ (0 : Int) + d3772 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2337, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20204 p hg
    simpa only [d2337, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2337, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2337, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20206 (p : Pattern) (guard : d5849 p = 1) : d2338 p ≤ (0 : Int) + d3773 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2338, d3773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20195 p hg
    simpa only [d2338, d3773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2338, d3773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20205 p hg
    simpa only [d2338, d3773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20207 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20208 (p : Pattern) (guard : d5843 p = 1) : d7 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20207 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20209 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (0 : Int) + d119 p := by
  omega
theorem compare20210 (p : Pattern) (guard : d5843 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20208 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20211 (p : Pattern) (guard : d5847 p = 1) : d120 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d120, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20208 p hg
    simpa only [d5847, d120, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d120, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d120, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20212 (p : Pattern) (guard : d5848 p = 1) : d120 p ≤ (0 : Int) + d3774 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20210 p hg
    simpa only [d5848, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20211 p hg
    simpa only [d5848, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20213 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3776 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20214 (p : Pattern) (guard : d5849 p = 1) : d2339 p ≤ (0 : Int) + d3777 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2339, d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20212 p hg
    simpa only [d5849, d2339, d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2339, d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20213 p hg
    simpa only [d5849, d2339, d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20215 (p : Pattern) (guard : d5849 p = 1) : d2340 p ≤ (0 : Int) + d3778 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2340, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20214 p hg
    simpa only [d2340, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2340, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2340, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20216 (p : Pattern) (guard : d5849 p = 1) : d2341 p ≤ (0 : Int) + d3779 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2341, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20195 p hg
    simpa only [d2341, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2341, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20215 p hg
    simpa only [d2341, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20217 (p : Pattern) (guard : d5849 p = 1) : d2342 p ≤ (0 : Int) + d3780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2342, d3780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20206 p hg
    simpa only [d2342, d3780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2342, d3780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20216 p hg
    simpa only [d2342, d3780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20218 (p : Pattern) (guard : d5849 p = 1) : d2343 p ≤ (0 : Int) + d3781 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2343, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20195 p hg
    simpa only [d2343, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2343, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2343, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20219 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20220 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d3782 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d3782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d107, d3782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d3782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20219 p hg
    simpa only [d5847, d107, d3782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20221 (p : Pattern) (guard : d5848 p = 1) : d107 p ≤ (0 : Int) + d3783 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d5848, d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20220 p hg
    simpa only [d5848, d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20222 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3784 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20223 (p : Pattern) (guard : d5849 p = 1) : d2328 p ≤ (0 : Int) + d3785 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2328, d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20221 p hg
    simpa only [d5849, d2328, d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2328, d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20222 p hg
    simpa only [d5849, d2328, d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20224 (p : Pattern) (guard : d5849 p = 1) : d2328 p ≤ (0 : Int) + d3786 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20171 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20223 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20225 (p : Pattern) (guard : d5849 p = 1) : d2344 p ≤ (0 : Int) + d3787 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2344, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20224 p hg
    simpa only [d2344, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2344, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2344, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20226 (p : Pattern) (guard : d5849 p = 1) : d2345 p ≤ (0 : Int) + d3788 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2345, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20218 p hg
    simpa only [d2345, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2345, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20225 p hg
    simpa only [d2345, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20227 (p : Pattern) (guard : d5849 p = 1) : d2346 p ≤ (0 : Int) + d3789 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2346, d3789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20217 p hg
    simpa only [d2346, d3789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2346, d3789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20226 p hg
    simpa only [d2346, d3789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20228 (p : Pattern) (guard : d5849 p = 1) : d2347 p ≤ (0 : Int) + d3790 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2347, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20019 p hg
    simpa only [d2347, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2347, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2347, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20229 (p : Pattern) (guard : d5849 p = 1) : d2348 p ≤ (0 : Int) + d3791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2348, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20226 p hg
    simpa only [d2348, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2348, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20228 p hg
    simpa only [d2348, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20230 (p : Pattern) (guard : d5849 p = 1) : d2349 p ≤ (0 : Int) + d3792 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2349, d3792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20227 p hg
    simpa only [d2349, d3792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2349, d3792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20229 p hg
    simpa only [d2349, d3792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20231 (p : Pattern) (guard : d5849 p = 1) : d2350 p ≤ (0 : Int) + d3793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2350, d3793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20189 p hg
    simpa only [d2350, d3793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2350, d3793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20230 p hg
    simpa only [d2350, d3793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20232 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20233 (p : Pattern) (guard : d5849 p = 1) : d2351 p ≤ (0 : Int) + d102 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20154 p hg
    simpa only [d5849, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20232 p hg
    simpa only [d5849, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20234 (p : Pattern) (guard : d5849 p = 1) : d2352 p ≤ (0 : Int) + d3745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2352, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20233 p hg
    simpa only [d2352, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2352, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20145 p hg
    simpa only [d2352, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20235 (p : Pattern) (guard : d5849 p = 1) : d2353 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2353, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20234 p hg
    simpa only [d2353, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2353, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20152 p hg
    simpa only [d2353, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20236 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d115 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14669 p hg
    simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20237 (p : Pattern) (guard : d5848 p = 1) : d116 p ≤ (0 : Int) + d115 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20236 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20238 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20239 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d115 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20237 p hg
    simpa only [d5849, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20238 p hg
    simpa only [d5849, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20240 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20241 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d3769 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d116, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20240 p hg
    simpa only [d5847, d116, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20242 (p : Pattern) (guard : d5848 p = 1) : d116 p ≤ (0 : Int) + d3794 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d5848, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20241 p hg
    simpa only [d5848, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20243 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3769 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20244 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d3795 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2336, d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20242 p hg
    simpa only [d5849, d2336, d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2336, d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20243 p hg
    simpa only [d5849, d2336, d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20245 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d3796 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20239 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20244 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20246 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20247 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d3797 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d3797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d116, d3797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d3797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20246 p hg
    simpa only [d5847, d116, d3797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20248 (p : Pattern) (guard : d5848 p = 1) : d116 p ≤ (0 : Int) + d3798 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d5848, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20247 p hg
    simpa only [d5848, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20249 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3797 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20250 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d3799 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2336, d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20248 p hg
    simpa only [d5849, d2336, d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2336, d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20249 p hg
    simpa only [d5849, d2336, d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20251 (p : Pattern) (guard : d5849 p = 1) : d2337 p ≤ (0 : Int) + d3800 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2337, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20250 p hg
    simpa only [d2337, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2337, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2337, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20252 (p : Pattern) (guard : d5849 p = 1) : d2354 p ≤ (0 : Int) + d3801 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2354, d3801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20245 p hg
    simpa only [d2354, d3801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2354, d3801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20251 p hg
    simpa only [d2354, d3801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20253 (p : Pattern) (guard : d5849 p = 1) : d2355 p ≤ (0 : Int) + d3802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2355, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20235 p hg
    simpa only [d2355, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2355, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20252 p hg
    simpa only [d2355, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20254 (p : Pattern) (guard : d5849 p = 1) : d2356 p ≤ (0 : Int) + d3803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2356, d3803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20184 p hg
    simpa only [d2356, d3803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2356, d3803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20003 p hg
    simpa only [d2356, d3803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20255 (p : Pattern) (guard : d5849 p = 1) : d2357 p ≤ (0 : Int) + d3804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2357, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20253 p hg
    simpa only [d2357, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2357, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20254 p hg
    simpa only [d2357, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20256 (p : Pattern) (guard : d5849 p = 1) : d2358 p ≤ (0 : Int) + d3805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2358, d3805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20184 p hg
    simpa only [d2358, d3805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2358, d3805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20010 p hg
    simpa only [d2358, d3805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20257 (p : Pattern) (guard : d5849 p = 1) : d2359 p ≤ (0 : Int) + d3806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2359, d3806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20256 p hg
    simpa only [d2359, d3806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2359, d3806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2359, d3806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20258 (p : Pattern) (guard : d5849 p = 1) : d2360 p ≤ (0 : Int) + d3807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2360, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20255 p hg
    simpa only [d2360, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2360, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20257 p hg
    simpa only [d2360, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20259 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d3808 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20239 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20204 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20260 (p : Pattern) (guard : d5849 p = 1) : d2361 p ≤ (0 : Int) + d3809 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2361, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20259 p hg
    simpa only [d2361, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2361, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2361, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20261 (p : Pattern) (guard : d5849 p = 1) : d2362 p ≤ (0 : Int) + d3810 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2362, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20216 p hg
    simpa only [d2362, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2362, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20260 p hg
    simpa only [d2362, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20262 (p : Pattern) (guard : d5849 p = 1) : d2363 p ≤ (0 : Int) + d3811 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2363, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20225 p hg
    simpa only [d2363, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2363, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20019 p hg
    simpa only [d2363, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20263 (p : Pattern) (guard : d5849 p = 1) : d2364 p ≤ (0 : Int) + d3812 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2364, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20261 p hg
    simpa only [d2364, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2364, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20262 p hg
    simpa only [d2364, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20264 (p : Pattern) (guard : d5849 p = 1) : d2365 p ≤ (0 : Int) + d3813 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2365, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20225 p hg
    simpa only [d2365, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2365, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20021 p hg
    simpa only [d2365, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20265 (p : Pattern) (guard : d5849 p = 1) : d2366 p ≤ (0 : Int) + d3814 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2366, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20264 p hg
    simpa only [d2366, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2366, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2366, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20266 (p : Pattern) (guard : d5849 p = 1) : d2367 p ≤ (0 : Int) + d3815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2367, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20263 p hg
    simpa only [d2367, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2367, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20265 p hg
    simpa only [d2367, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20267 (p : Pattern) (guard : d5849 p = 1) : d2368 p ≤ (0 : Int) + d3816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2368, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20258 p hg
    simpa only [d2368, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2368, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20266 p hg
    simpa only [d2368, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20268 (p : Pattern) (guard : d5849 p = 1) : d2369 p ≤ (0 : Int) + d3817 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2369, d3817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20231 p hg
    simpa only [d2369, d3817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2369, d3817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20267 p hg
    simpa only [d2369, d3817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20269 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3818 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20270 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3819 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2319, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20192 p hg
    simpa only [d5849, d2319, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2319, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20269 p hg
    simpa only [d5849, d2319, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20271 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3820 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20161 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20270 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20272 (p : Pattern) (guard : d5849 p = 1) : d2321 p ≤ (0 : Int) + d3821 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20145 p hg
    simpa only [d2321, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2321, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20273 (p : Pattern) (guard : d5849 p = 1) : d2327 p ≤ (0 : Int) + d3822 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20271 p hg
    simpa only [d2327, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20272 p hg
    simpa only [d2327, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20274 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3824 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20275 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3825 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2319, d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20192 p hg
    simpa only [d5849, d2319, d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2319, d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20274 p hg
    simpa only [d5849, d2319, d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20276 (p : Pattern) (guard : d5849 p = 1) : d2321 p ≤ (0 : Int) + d3826 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20275 p hg
    simpa only [d2321, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2321, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20277 (p : Pattern) (guard : d5849 p = 1) : d2327 p ≤ (0 : Int) + d3827 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20195 p hg
    simpa only [d2327, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20276 p hg
    simpa only [d2327, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20278 (p : Pattern) (guard : d5849 p = 1) : d2327 p ≤ (0 : Int) + d3828 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20273 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20277 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20279 (p : Pattern) (guard : d5849 p = 1) : d2321 p ≤ (0 : Int) + d3829 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20194 p hg
    simpa only [d2321, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2321, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20280 (p : Pattern) (guard : d5849 p = 1) : d2327 p ≤ (0 : Int) + d3830 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20195 p hg
    simpa only [d2327, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20279 p hg
    simpa only [d2327, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20281 (p : Pattern) (guard : d5849 p = 1) : d2329 p ≤ (0 : Int) + d3831 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2329, d3831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20223 p hg
    simpa only [d2329, d3831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2329, d3831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2329, d3831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20282 (p : Pattern) (guard : d5849 p = 1) : d2330 p ≤ (0 : Int) + d3832 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2330, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20224 p hg
    simpa only [d2330, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2330, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20281 p hg
    simpa only [d2330, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20283 (p : Pattern) (guard : d5849 p = 1) : d2331 p ≤ (0 : Int) + d3833 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2331, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20280 p hg
    simpa only [d2331, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2331, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20282 p hg
    simpa only [d2331, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20284 (p : Pattern) (guard : d5849 p = 1) : d2370 p ≤ (0 : Int) + d3834 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2370, d3834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20278 p hg
    simpa only [d2370, d3834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2370, d3834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20283 p hg
    simpa only [d2370, d3834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20285 (p : Pattern) (guard : d5849 p = 1) : d2334 p ≤ (0 : Int) + d3835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2334, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20283 p hg
    simpa only [d2334, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2334, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20187 p hg
    simpa only [d2334, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20286 (p : Pattern) (guard : d5849 p = 1) : d2371 p ≤ (0 : Int) + d3836 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2371, d3836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20284 p hg
    simpa only [d2371, d3836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2371, d3836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20285 p hg
    simpa only [d2371, d3836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20287 (p : Pattern) (guard : d5849 p = 1) : d2354 p ≤ (0 : Int) + d3837 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2354, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20259 p hg
    simpa only [d2354, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2354, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20205 p hg
    simpa only [d2354, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20288 (p : Pattern) (guard : d5847 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20208 p hg
    simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14677 p hg
    simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20289 (p : Pattern) (guard : d5848 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20210 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20288 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20290 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20291 (p : Pattern) (guard : d5849 p = 1) : d2339 p ≤ (0 : Int) + d119 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20289 p hg
    simpa only [d5849, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5849, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20292 (p : Pattern) (guard : d5849 p = 1) : d2339 p ≤ (0 : Int) + d3838 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20291 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20214 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20293 (p : Pattern) (guard : d5849 p = 1) : d2372 p ≤ (0 : Int) + d3839 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2372, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20292 p hg
    simpa only [d2372, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2372, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20215 p hg
    simpa only [d2372, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20294 (p : Pattern) (guard : d5849 p = 1) : d2373 p ≤ (0 : Int) + d3840 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2373, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20287 p hg
    simpa only [d2373, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2373, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20293 p hg
    simpa only [d2373, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20295 (p : Pattern) (guard : d5849 p = 1) : d2374 p ≤ (0 : Int) + d3841 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2374, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20294 p hg
    simpa only [d2374, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2374, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2374, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20296 (p : Pattern) (guard : d5849 p = 1) : d2375 p ≤ (0 : Int) + d3842 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2375, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20295 p hg
    simpa only [d2375, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2375, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2375, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20297 (p : Pattern) (guard : d5849 p = 1) : d2376 p ≤ (0 : Int) + d3843 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2376, d3843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20286 p hg
    simpa only [d2376, d3843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2376, d3843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20296 p hg
    simpa only [d2376, d3843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20298 (p : Pattern) (guard : d5849 p = 1) : d2377 p ≤ (0 : Int) + d3844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2377, d3844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20277 p hg
    simpa only [d2377, d3844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2377, d3844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20287 p hg
    simpa only [d2377, d3844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20299 (p : Pattern) (guard : d5849 p = 1) : d2356 p ≤ (0 : Int) + d3845 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2356, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20282 p hg
    simpa only [d2356, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2356, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20003 p hg
    simpa only [d2356, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
