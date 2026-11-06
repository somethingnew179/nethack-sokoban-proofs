/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons204
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28700 (p : Pattern) (guard : d5268 p = 1) : d3519 p ≤ (0 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3519, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28445 p hg
    simpa only [d3519, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3519, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3519, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28701 (p : Pattern) (guard : d5268 p = 1) : d3520 p ≤ (0 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3520, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28700 p hg
    simpa only [d3520, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3520, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3520, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28702 (p : Pattern) (guard : d5268 p = 1) : d3521 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3521, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28699 p hg
    simpa only [d3521, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3521, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28701 p hg
    simpa only [d3521, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28703 (p : Pattern) (guard : d5268 p = 1) : d3522 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3522, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28697 p hg
    simpa only [d3522, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3522, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28702 p hg
    simpa only [d3522, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28704 (p : Pattern) (guard : d5268 p = 1) : d3523 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3523, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28693 p hg
    simpa only [d3523, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3523, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28703 p hg
    simpa only [d3523, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28705 (p : Pattern) (guard : d5268 p = 1) : d3524 p ≤ (0 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3524, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28576 p hg
    simpa only [d3524, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3524, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28444 p hg
    simpa only [d3524, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28706 (p : Pattern) (guard : d5268 p = 1) : d3525 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3525, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28551 p hg
    simpa only [d3525, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3525, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28705 p hg
    simpa only [d3525, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28707 (p : Pattern) (guard : d5268 p = 1) : d3526 p ≤ (0 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3526, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28554 p hg
    simpa only [d3526, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3526, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28444 p hg
    simpa only [d3526, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28708 (p : Pattern) (guard : d5268 p = 1) : d3527 p ≤ (0 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3527, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28707 p hg
    simpa only [d3527, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3527, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3527, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28709 (p : Pattern) (guard : d5268 p = 1) : d3528 p ≤ (0 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3528, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28706 p hg
    simpa only [d3528, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3528, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28708 p hg
    simpa only [d3528, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28710 (p : Pattern) (guard : d5268 p = 1) : d3529 p ≤ (0 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3529, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28594 p hg
    simpa only [d3529, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3529, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28475 p hg
    simpa only [d3529, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28711 (p : Pattern) (guard : d5268 p = 1) : d3530 p ≤ (0 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3530, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28710 p hg
    simpa only [d3530, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3530, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3530, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28712 (p : Pattern) (guard : d5268 p = 1) : d3531 p ≤ (0 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3531, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28711 p hg
    simpa only [d3531, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3531, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3531, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28713 (p : Pattern) (guard : d5268 p = 1) : d3532 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3532, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28709 p hg
    simpa only [d3532, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3532, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28712 p hg
    simpa only [d3532, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28714 (p : Pattern) (guard : d5268 p = 1) : d3533 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3533, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28713 p hg
    simpa only [d3533, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3533, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28702 p hg
    simpa only [d3533, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28715 (p : Pattern) (guard : d5268 p = 1) : d3534 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3534, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28714 p hg
    simpa only [d3534, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3534, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3534, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28716 (p : Pattern) (guard : d5268 p = 1) : d3535 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3535, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28704 p hg
    simpa only [d3535, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3535, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28715 p hg
    simpa only [d3535, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28717 (p : Pattern) (guard : d5268 p = 1) : d3536 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3536, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28678 p hg
    simpa only [d3536, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3536, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28716 p hg
    simpa only [d3536, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28718 (p : Pattern) (guard : d5268 p = 1) : d3537 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3537, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28526 p hg
    simpa only [d3537, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3537, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28717 p hg
    simpa only [d3537, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28719 (p : Pattern) (guard : d5268 p = 1) : d3538 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3538, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28661 p hg
    simpa only [d3538, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3538, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28718 p hg
    simpa only [d3538, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28720 (p : Pattern) (guard : d5268 p = 1) : d3539 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3539, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28622 p hg
    simpa only [d3539, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3539, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28719 p hg
    simpa only [d3539, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28721 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28722 (p : Pattern) (guard : d5851 p = 1) : d3227 p ≤ (0 : Int) + d2503 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d3227, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26604 p hg
    simpa only [d5851, d3227, d2503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d3227, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28721 p hg
    simpa only [d5851, d3227, d2503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28723 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23364 p hg
    simpa only [d5847, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19882 p hg
    simpa only [d5847, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28724 (p : Pattern) (guard : d5854 p = 1) : d3226 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28723 p hg
    simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28725 (p : Pattern) (guard : d5855 p = 1) : d3228 p ≤ (0 : Int) + d2505 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d3228, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28722 p hg
    simpa only [d5855, d3228, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d3228, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28724 p hg
    simpa only [d5855, d3228, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28726 (p : Pattern) (guard : d5851 p = 1) : d3226 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d5851, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5851, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28727 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28728 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d1769 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28727 p hg
    simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28729 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d1770 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28728 p hg
    simpa only [d5847, d3226, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5847, d3226, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28730 (p : Pattern) (guard : d5854 p = 1) : d3226 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28729 p hg
    simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28731 (p : Pattern) (guard : d5855 p = 1) : d3226 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28726 p hg
    simpa only [d5855, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28730 p hg
    simpa only [d5855, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28732 (p : Pattern) (guard : d5855 p = 1) : d3229 p ≤ (0 : Int) + d2508 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3229, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28725 p hg
    simpa only [d3229, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3229, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28731 p hg
    simpa only [d3229, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28733 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28734 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d1683 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28733 p hg
    simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28735 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d1684 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28734 p hg
    simpa only [d5847, d3226, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19972 p hg
    simpa only [d5847, d3226, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28736 (p : Pattern) (guard : d5854 p = 1) : d3226 p ≤ (0 : Int) + d2509 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28735 p hg
    simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28737 (p : Pattern) (guard : d5855 p = 1) : d3226 p ≤ (0 : Int) + d2510 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28726 p hg
    simpa only [d5855, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28736 p hg
    simpa only [d5855, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28738 (p : Pattern) (guard : d5855 p = 1) : d3230 p ≤ (0 : Int) + d2511 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3230, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28737 p hg
    simpa only [d3230, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3230, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3230, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28739 (p : Pattern) (guard : d5855 p = 1) : d3231 p ≤ (0 : Int) + d2512 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3231, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28732 p hg
    simpa only [d3231, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3231, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28738 p hg
    simpa only [d3231, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28740 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28741 (p : Pattern) (guard : d5851 p = 1) : d3233 p ≤ (0 : Int) + d2513 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d3233, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26615 p hg
    simpa only [d5851, d3233, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d3233, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28740 p hg
    simpa only [d5851, d3233, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28742 (p : Pattern) (guard : d5855 p = 1) : d3234 p ≤ (0 : Int) + d2514 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d3234, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28741 p hg
    simpa only [d5855, d3234, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d3234, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28724 p hg
    simpa only [d5855, d3234, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28743 (p : Pattern) (guard : d5855 p = 1) : d3235 p ≤ (0 : Int) + d2515 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3235, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28742 p hg
    simpa only [d3235, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3235, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28731 p hg
    simpa only [d3235, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28744 (p : Pattern) (guard : d5855 p = 1) : d3236 p ≤ (0 : Int) + d2516 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3236, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28743 p hg
    simpa only [d3236, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3236, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28738 p hg
    simpa only [d3236, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28745 (p : Pattern) (guard : d5855 p = 1) : d3237 p ≤ (0 : Int) + d2517 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3237, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28739 p hg
    simpa only [d3237, d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3237, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28744 p hg
    simpa only [d3237, d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28746 (p : Pattern) (guard : d5855 p = 1) : d3226 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28726 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28724 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28747 (p : Pattern) (guard : d5855 p = 1) : d3226 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28746 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28731 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28748 (p : Pattern) (guard : d5855 p = 1) : d3238 p ≤ (0 : Int) + d2519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3238, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28747 p hg
    simpa only [d3238, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3238, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28738 p hg
    simpa only [d3238, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28749 (p : Pattern) (guard : d5851 p = 1) : d3239 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26626 p hg
    simpa only [d5851, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5851, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28750 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23393 p hg
    simpa only [d5847, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5847, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28751 (p : Pattern) (guard : d5854 p = 1) : d3239 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28750 p hg
    simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28752 (p : Pattern) (guard : d5855 p = 1) : d3239 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28749 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28751 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28753 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28754 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (0 : Int) + d1794 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28753 p hg
    simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28755 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d1795 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28754 p hg
    simpa only [d5847, d3239, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5847, d3239, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28756 (p : Pattern) (guard : d5854 p = 1) : d3239 p ≤ (0 : Int) + d2521 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28755 p hg
    simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28757 (p : Pattern) (guard : d5855 p = 1) : d3239 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28749 p hg
    simpa only [d5855, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28756 p hg
    simpa only [d5855, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28758 (p : Pattern) (guard : d5855 p = 1) : d3239 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28752 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28757 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28759 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28760 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (0 : Int) + d1693 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28759 p hg
    simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28761 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d1694 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28760 p hg
    simpa only [d5847, d3239, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5847, d3239, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28762 (p : Pattern) (guard : d5854 p = 1) : d3239 p ≤ (0 : Int) + d2524 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28761 p hg
    simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28763 (p : Pattern) (guard : d5855 p = 1) : d3239 p ≤ (0 : Int) + d2525 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28749 p hg
    simpa only [d5855, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28762 p hg
    simpa only [d5855, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28764 (p : Pattern) (guard : d5855 p = 1) : d3240 p ≤ (0 : Int) + d2526 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3240, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28763 p hg
    simpa only [d3240, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3240, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3240, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28765 (p : Pattern) (guard : d5855 p = 1) : d3241 p ≤ (0 : Int) + d2527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3241, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28758 p hg
    simpa only [d3241, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3241, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28764 p hg
    simpa only [d3241, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28766 (p : Pattern) (guard : d5855 p = 1) : d3242 p ≤ (0 : Int) + d2528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3242, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28748 p hg
    simpa only [d3242, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3242, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28765 p hg
    simpa only [d3242, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28767 (p : Pattern) (guard : d5855 p = 1) : d3243 p ≤ (0 : Int) + d2529 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3243, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28745 p hg
    simpa only [d3243, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3243, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28766 p hg
    simpa only [d3243, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28768 (p : Pattern) (guard : d5851 p = 1) : d3244 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26635 p hg
    simpa only [d5851, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d5851, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28769 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23413 p hg
    simpa only [d5847, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5847, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28770 (p : Pattern) (guard : d5854 p = 1) : d3244 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28769 p hg
    simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28771 (p : Pattern) (guard : d5855 p = 1) : d3244 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28768 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28770 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28772 (p : Pattern) (guard : d5854 p = 1) : d3244 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27353 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28773 (p : Pattern) (guard : d5855 p = 1) : d3244 p ≤ (0 : Int) + d2531 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28768 p hg
    simpa only [d5855, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28772 p hg
    simpa only [d5855, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28774 (p : Pattern) (guard : d5855 p = 1) : d3244 p ≤ (0 : Int) + d2532 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28771 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28773 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28775 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28776 (p : Pattern) (guard : d5843 p = 1) : d9 p ≤ (0 : Int) + d1701 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28775 p hg
    simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28777 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d1702 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3244, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28776 p hg
    simpa only [d5847, d3244, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3244, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3244, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28778 (p : Pattern) (guard : d5854 p = 1) : d3244 p ≤ (0 : Int) + d2533 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28777 p hg
    simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28779 (p : Pattern) (guard : d5855 p = 1) : d3244 p ≤ (0 : Int) + d2534 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28768 p hg
    simpa only [d5855, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28778 p hg
    simpa only [d5855, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28780 (p : Pattern) (guard : d5855 p = 1) : d3245 p ≤ (0 : Int) + d2535 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3245, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28779 p hg
    simpa only [d3245, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3245, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3245, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28781 (p : Pattern) (guard : d5855 p = 1) : d3246 p ≤ (0 : Int) + d2536 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3246, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28774 p hg
    simpa only [d3246, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3246, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28780 p hg
    simpa only [d3246, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28782 (p : Pattern) (guard : d5855 p = 1) : d3247 p ≤ (0 : Int) + d2537 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3247, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28781 p hg
    simpa only [d3247, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3247, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3247, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28783 (p : Pattern) (guard : d5855 p = 1) : d3248 p ≤ (0 : Int) + d2538 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3248, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28766 p hg
    simpa only [d3248, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3248, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28782 p hg
    simpa only [d3248, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28784 (p : Pattern) (guard : d5855 p = 1) : d3249 p ≤ (0 : Int) + d2539 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3249, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28767 p hg
    simpa only [d3249, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3249, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28783 p hg
    simpa only [d3249, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28785 (p : Pattern) (guard : d5851 p = 1) : d3250 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26643 p hg
    simpa only [d5851, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5851, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28786 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28787 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d1713 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28786 p hg
    simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28788 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d1714 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28787 p hg
    simpa only [d5847, d3250, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5847, d3250, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28789 (p : Pattern) (guard : d5854 p = 1) : d3250 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28788 p hg
    simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28790 (p : Pattern) (guard : d5855 p = 1) : d3250 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28785 p hg
    simpa only [d5855, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28789 p hg
    simpa only [d5855, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28791 (p : Pattern) (guard : d5855 p = 1) : d3251 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3251, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28790 p hg
    simpa only [d3251, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3251, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3251, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28792 (p : Pattern) (guard : d5855 p = 1) : d3252 p ≤ (0 : Int) + d2544 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3252, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28747 p hg
    simpa only [d3252, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3252, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28791 p hg
    simpa only [d3252, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28793 (p : Pattern) (guard : d5851 p = 1) : d3253 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26648 p hg
    simpa only [d5851, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26649 p hg
    simpa only [d5851, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28794 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28795 (p : Pattern) (guard : d5843 p = 1) : d6 p ≤ (0 : Int) + d1721 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28794 p hg
    simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28796 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d1722 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3253, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28795 p hg
    simpa only [d5847, d3253, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3253, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5847, d3253, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28797 (p : Pattern) (guard : d5854 p = 1) : d3253 p ≤ (0 : Int) + d2546 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28796 p hg
    simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26649 p hg
    simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28798 (p : Pattern) (guard : d5855 p = 1) : d3253 p ≤ (0 : Int) + d2547 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28793 p hg
    simpa only [d5855, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28797 p hg
    simpa only [d5855, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28799 (p : Pattern) (guard : d5855 p = 1) : d3254 p ≤ (0 : Int) + d2548 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3254, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28798 p hg
    simpa only [d3254, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3254, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3254, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28800 (p : Pattern) (guard : d5855 p = 1) : d3255 p ≤ (0 : Int) + d2549 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3255, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28747 p hg
    simpa only [d3255, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3255, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28799 p hg
    simpa only [d3255, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28801 (p : Pattern) (guard : d5855 p = 1) : d3256 p ≤ (0 : Int) + d2550 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3256, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28792 p hg
    simpa only [d3256, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3256, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28800 p hg
    simpa only [d3256, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28802 (p : Pattern) (guard : d5851 p = 1) : d3257 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26654 p hg
    simpa only [d5851, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d5851, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28803 (p : Pattern) (guard : d5854 p = 1) : d3257 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27390 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28804 (p : Pattern) (guard : d5855 p = 1) : d3257 p ≤ (0 : Int) + d2552 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28802 p hg
    simpa only [d5855, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28803 p hg
    simpa only [d5855, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28805 (p : Pattern) (guard : d5855 p = 1) : d3258 p ≤ (0 : Int) + d2553 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3258, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28804 p hg
    simpa only [d3258, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3258, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3258, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28806 (p : Pattern) (guard : d5855 p = 1) : d3259 p ≤ (0 : Int) + d2554 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3259, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28747 p hg
    simpa only [d3259, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3259, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28805 p hg
    simpa only [d3259, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28807 (p : Pattern) (guard : d5855 p = 1) : d3260 p ≤ (0 : Int) + d2555 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3260, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28758 p hg
    simpa only [d3260, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3260, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3260, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28808 (p : Pattern) (guard : d5855 p = 1) : d3261 p ≤ (0 : Int) + d2556 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3261, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28806 p hg
    simpa only [d3261, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3261, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28807 p hg
    simpa only [d3261, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28809 (p : Pattern) (guard : d5855 p = 1) : d3262 p ≤ (0 : Int) + d2557 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3262, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28801 p hg
    simpa only [d3262, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3262, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28808 p hg
    simpa only [d3262, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28810 (p : Pattern) (guard : d5855 p = 1) : d3263 p ≤ (0 : Int) + d2558 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3263, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28747 p hg
    simpa only [d3263, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3263, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3263, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28811 (p : Pattern) (guard : d5855 p = 1) : d3264 p ≤ (0 : Int) + d2559 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3264, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28810 p hg
    simpa only [d3264, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3264, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28807 p hg
    simpa only [d3264, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28812 (p : Pattern) (guard : d5855 p = 1) : d3265 p ≤ (0 : Int) + d2560 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3265, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28774 p hg
    simpa only [d3265, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3265, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3265, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28813 (p : Pattern) (guard : d5855 p = 1) : d3266 p ≤ (0 : Int) + d2561 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3266, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28812 p hg
    simpa only [d3266, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3266, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3266, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28814 (p : Pattern) (guard : d5855 p = 1) : d3267 p ≤ (0 : Int) + d2562 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3267, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28811 p hg
    simpa only [d3267, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3267, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28813 p hg
    simpa only [d3267, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28815 (p : Pattern) (guard : d5855 p = 1) : d3268 p ≤ (0 : Int) + d2563 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3268, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28809 p hg
    simpa only [d3268, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3268, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28814 p hg
    simpa only [d3268, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28816 (p : Pattern) (guard : d5855 p = 1) : d3269 p ≤ (0 : Int) + d2564 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3269, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28784 p hg
    simpa only [d3269, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3269, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28815 p hg
    simpa only [d3269, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28817 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (0 : Int) + d329 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28818 (p : Pattern) (guard : d5851 p = 1) : d3271 p ≤ (0 : Int) + d2565 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d3271, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26670 p hg
    simpa only [d5851, d3271, d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d3271, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28817 p hg
    simpa only [d5851, d3271, d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28819 (p : Pattern) (guard : d5855 p = 1) : d3272 p ≤ (0 : Int) + d2566 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d3272, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28818 p hg
    simpa only [d5855, d3272, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d3272, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28724 p hg
    simpa only [d5855, d3272, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28820 (p : Pattern) (guard : d5855 p = 1) : d3273 p ≤ (0 : Int) + d2567 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3273, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28819 p hg
    simpa only [d3273, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3273, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28731 p hg
    simpa only [d3273, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28821 (p : Pattern) (guard : d5855 p = 1) : d3274 p ≤ (0 : Int) + d2568 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3274, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28820 p hg
    simpa only [d3274, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3274, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28738 p hg
    simpa only [d3274, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28822 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23473 p hg
    simpa only [d5847, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19972 p hg
    simpa only [d5847, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28823 (p : Pattern) (guard : d5854 p = 1) : d3250 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28822 p hg
    simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28824 (p : Pattern) (guard : d5855 p = 1) : d3250 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28785 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28823 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28825 (p : Pattern) (guard : d5855 p = 1) : d3250 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28824 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28790 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28826 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28827 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d1742 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28826 p hg
    simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28828 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d1743 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28827 p hg
    simpa only [d5847, d3250, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5847, d3250, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28829 (p : Pattern) (guard : d5854 p = 1) : d3250 p ≤ (0 : Int) + d2570 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28828 p hg
    simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28830 (p : Pattern) (guard : d5855 p = 1) : d3250 p ≤ (0 : Int) + d2571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28785 p hg
    simpa only [d5855, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28829 p hg
    simpa only [d5855, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28831 (p : Pattern) (guard : d5855 p = 1) : d3251 p ≤ (0 : Int) + d2572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3251, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28830 p hg
    simpa only [d3251, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3251, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3251, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28832 (p : Pattern) (guard : d5855 p = 1) : d3275 p ≤ (0 : Int) + d2573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3275, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28825 p hg
    simpa only [d3275, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3275, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28831 p hg
    simpa only [d3275, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28833 (p : Pattern) (guard : d5855 p = 1) : d3276 p ≤ (0 : Int) + d2574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3276, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28821 p hg
    simpa only [d3276, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3276, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28832 p hg
    simpa only [d3276, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28834 (p : Pattern) (guard : d5855 p = 1) : d3277 p ≤ (0 : Int) + d2575 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3277, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28765 p hg
    simpa only [d3277, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3277, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28781 p hg
    simpa only [d3277, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28835 (p : Pattern) (guard : d5855 p = 1) : d3278 p ≤ (0 : Int) + d2576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3278, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28833 p hg
    simpa only [d3278, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3278, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28834 p hg
    simpa only [d3278, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28836 (p : Pattern) (guard : d5851 p = 1) : d3279 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26680 p hg
    simpa only [d5851, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d5851, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28837 (p : Pattern) (guard : d5847 p = 1) : d3279 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23489 p hg
    simpa only [d5847, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5847, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28838 (p : Pattern) (guard : d5854 p = 1) : d3279 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28837 p hg
    simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28839 (p : Pattern) (guard : d5855 p = 1) : d3279 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28836 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28838 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
