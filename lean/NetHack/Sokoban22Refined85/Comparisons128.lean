/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons127
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17920 (p : Pattern) (guard : d5268 p = 1) : d214 p ≤ (0 : Int) + d3484 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d214, d3484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17918 p hg
    simpa only [d214, d3484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d214, d3484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17919 p hg
    simpa only [d214, d3484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17921 (p : Pattern) (guard : d5268 p = 1) : d215 p ≤ (0 : Int) + d3485 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d215, d3485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17816 p hg
    simpa only [d215, d3485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d215, d3485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d215, d3485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17922 (p : Pattern) (guard : d5268 p = 1) : d216 p ≤ (0 : Int) + d3486 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d216, d3486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17837 p hg
    simpa only [d216, d3486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d216, d3486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17921 p hg
    simpa only [d216, d3486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17923 (p : Pattern) (guard : d5268 p = 1) : d217 p ≤ (0 : Int) + d3487 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d217, d3487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17921 p hg
    simpa only [d217, d3487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d217, d3487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d217, d3487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17924 (p : Pattern) (guard : d5268 p = 1) : d218 p ≤ (0 : Int) + d3488 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d218, d3488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17922 p hg
    simpa only [d218, d3488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d218, d3488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17923 p hg
    simpa only [d218, d3488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17925 (p : Pattern) (guard : d5268 p = 1) : d219 p ≤ (0 : Int) + d3489 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d219, d3489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17920 p hg
    simpa only [d219, d3489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d219, d3489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17924 p hg
    simpa only [d219, d3489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17926 (p : Pattern) (guard : d5268 p = 1) : d220 p ≤ (0 : Int) + d3490 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d220, d3490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17822 p hg
    simpa only [d220, d3490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d220, d3490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17925 p hg
    simpa only [d220, d3490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17927 (p : Pattern) (guard : d5268 p = 1) : d212 p ≤ (0 : Int) + d3491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d212, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17852 p hg
    simpa only [d212, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d212, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17917 p hg
    simpa only [d212, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17928 (p : Pattern) (guard : d5268 p = 1) : d214 p ≤ (0 : Int) + d3492 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d214, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17927 p hg
    simpa only [d214, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d214, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17919 p hg
    simpa only [d214, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17929 (p : Pattern) (guard : d5268 p = 1) : d221 p ≤ (0 : Int) + d3493 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d221, d3493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17928 p hg
    simpa only [d221, d3493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d221, d3493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17857 p hg
    simpa only [d221, d3493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17930 (p : Pattern) (guard : d5268 p = 1) : d222 p ≤ (0 : Int) + d3494 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d222, d3494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17851 p hg
    simpa only [d222, d3494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d222, d3494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17929 p hg
    simpa only [d222, d3494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17931 (p : Pattern) (guard : d5268 p = 1) : d223 p ≤ (0 : Int) + d3495 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d223, d3495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17926 p hg
    simpa only [d223, d3495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d223, d3495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17930 p hg
    simpa only [d223, d3495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17932 (p : Pattern) (guard : d5268 p = 1) : d224 p ≤ (0 : Int) + d3496 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d224, d3496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17930 p hg
    simpa only [d224, d3496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d224, d3496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17864 p hg
    simpa only [d224, d3496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17933 (p : Pattern) (guard : d5268 p = 1) : d225 p ≤ (0 : Int) + d3497 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d225, d3497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17931 p hg
    simpa only [d225, d3497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d225, d3497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17932 p hg
    simpa only [d225, d3497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17934 (p : Pattern) (guard : d5268 p = 1) : d226 p ≤ (0 : Int) + d3498 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d226, d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17807 p hg
    simpa only [d226, d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d226, d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17812 p hg
    simpa only [d226, d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17935 (p : Pattern) (guard : d5268 p = 1) : d227 p ≤ (0 : Int) + d3499 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d227, d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17829 p hg
    simpa only [d227, d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d227, d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17934 p hg
    simpa only [d227, d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17936 (p : Pattern) (guard : d5268 p = 1) : d228 p ≤ (0 : Int) + d3500 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d228, d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d228, d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d228, d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17921 p hg
    simpa only [d228, d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17937 (p : Pattern) (guard : d5268 p = 1) : d229 p ≤ (0 : Int) + d3501 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d229, d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17811 p hg
    simpa only [d229, d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d229, d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d229, d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17938 (p : Pattern) (guard : d5268 p = 1) : d230 p ≤ (0 : Int) + d3502 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d230, d3502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d230, d3502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d230, d3502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d230, d3502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17939 (p : Pattern) (guard : d5268 p = 1) : d231 p ≤ (0 : Int) + d3503 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d231, d3503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d231, d3503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d231, d3503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d231, d3503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17940 (p : Pattern) (guard : d5268 p = 1) : d232 p ≤ (0 : Int) + d3504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d232, d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d232, d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d232, d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d232, d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17941 (p : Pattern) (guard : d5268 p = 1) : d233 p ≤ (0 : Int) + d3505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d233, d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17846 p hg
    simpa only [d233, d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d233, d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d233, d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17942 (p : Pattern) (guard : d5268 p = 1) : d234 p ≤ (0 : Int) + d3506 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d234, d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17798 p hg
    simpa only [d234, d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d234, d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17812 p hg
    simpa only [d234, d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17943 (p : Pattern) (guard : d5268 p = 1) : d235 p ≤ (0 : Int) + d3507 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d235, d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d235, d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d235, d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17816 p hg
    simpa only [d235, d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17944 (p : Pattern) (guard : d5268 p = 1) : d236 p ≤ (0 : Int) + d3508 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d236, d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17943 p hg
    simpa only [d236, d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d236, d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d236, d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17945 (p : Pattern) (guard : d5268 p = 1) : d237 p ≤ (0 : Int) + d3509 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d237, d3509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17692 p hg
    simpa only [d237, d3509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d237, d3509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d237, d3509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17946 (p : Pattern) (guard : d5268 p = 1) : d238 p ≤ (0 : Int) + d3510 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d238, d3510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d238, d3510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d238, d3510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17945 p hg
    simpa only [d238, d3510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17947 (p : Pattern) (guard : d5268 p = 1) : d239 p ≤ (0 : Int) + d3511 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d239, d3511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17928 p hg
    simpa only [d239, d3511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d239, d3511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17946 p hg
    simpa only [d239, d3511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17948 (p : Pattern) (guard : d5268 p = 1) : d240 p ≤ (0 : Int) + d3512 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d240, d3512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17941 p hg
    simpa only [d240, d3512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d240, d3512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d240, d3512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17949 (p : Pattern) (guard : d5268 p = 1) : d241 p ≤ (0 : Int) + d3513 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d241, d3513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17829 p hg
    simpa only [d241, d3513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d241, d3513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17711 p hg
    simpa only [d241, d3513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17950 (p : Pattern) (guard : d5268 p = 1) : d242 p ≤ (0 : Int) + d3514 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d242, d3514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17795 p hg
    simpa only [d242, d3514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d242, d3514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d242, d3514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17951 (p : Pattern) (guard : d5268 p = 1) : d243 p ≤ (0 : Int) + d3515 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d243, d3515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17950 p hg
    simpa only [d243, d3515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d243, d3515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17834 p hg
    simpa only [d243, d3515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17952 (p : Pattern) (guard : d5268 p = 1) : d244 p ≤ (0 : Int) + d3516 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d244, d3516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17951 p hg
    simpa only [d244, d3516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d244, d3516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17857 p hg
    simpa only [d244, d3516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17953 (p : Pattern) (guard : d5268 p = 1) : d245 p ≤ (0 : Int) + d3517 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d245, d3517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17829 p hg
    simpa only [d245, d3517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d245, d3517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17917 p hg
    simpa only [d245, d3517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17954 (p : Pattern) (guard : d5268 p = 1) : d246 p ≤ (0 : Int) + d3518 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d246, d3518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17953 p hg
    simpa only [d246, d3518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d246, d3518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17856 p hg
    simpa only [d246, d3518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17955 (p : Pattern) (guard : d5268 p = 1) : d247 p ≤ (0 : Int) + d3519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d247, d3519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17670 p hg
    simpa only [d247, d3519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d247, d3519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d247, d3519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17956 (p : Pattern) (guard : d5268 p = 1) : d248 p ≤ (0 : Int) + d3520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d248, d3520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d248, d3520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d248, d3520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d248, d3520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17957 (p : Pattern) (guard : d5268 p = 1) : d249 p ≤ (0 : Int) + d3521 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d249, d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17954 p hg
    simpa only [d249, d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d249, d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17956 p hg
    simpa only [d249, d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17958 (p : Pattern) (guard : d5268 p = 1) : d250 p ≤ (0 : Int) + d3522 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d250, d3522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17952 p hg
    simpa only [d250, d3522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d250, d3522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17957 p hg
    simpa only [d250, d3522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17959 (p : Pattern) (guard : d5268 p = 1) : d251 p ≤ (0 : Int) + d3523 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d251, d3523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17948 p hg
    simpa only [d251, d3523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d251, d3523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17958 p hg
    simpa only [d251, d3523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17960 (p : Pattern) (guard : d5268 p = 1) : d252 p ≤ (0 : Int) + d3524 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d252, d3524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17829 p hg
    simpa only [d252, d3524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d252, d3524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17669 p hg
    simpa only [d252, d3524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17961 (p : Pattern) (guard : d5268 p = 1) : d253 p ≤ (0 : Int) + d3525 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d253, d3525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17795 p hg
    simpa only [d253, d3525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d253, d3525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17960 p hg
    simpa only [d253, d3525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17962 (p : Pattern) (guard : d5268 p = 1) : d254 p ≤ (0 : Int) + d3526 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d254, d3526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17800 p hg
    simpa only [d254, d3526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d254, d3526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17669 p hg
    simpa only [d254, d3526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17963 (p : Pattern) (guard : d5268 p = 1) : d255 p ≤ (0 : Int) + d3527 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d255, d3527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17962 p hg
    simpa only [d255, d3527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d255, d3527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d255, d3527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17964 (p : Pattern) (guard : d5268 p = 1) : d256 p ≤ (0 : Int) + d3528 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d256, d3528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17961 p hg
    simpa only [d256, d3528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d256, d3528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17963 p hg
    simpa only [d256, d3528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17965 (p : Pattern) (guard : d5268 p = 1) : d257 p ≤ (0 : Int) + d3529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d257, d3529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17847 p hg
    simpa only [d257, d3529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d257, d3529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17711 p hg
    simpa only [d257, d3529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17966 (p : Pattern) (guard : d5268 p = 1) : d258 p ≤ (0 : Int) + d3530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d258, d3530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17965 p hg
    simpa only [d258, d3530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d258, d3530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d258, d3530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17967 (p : Pattern) (guard : d5268 p = 1) : d259 p ≤ (0 : Int) + d3531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d259, d3531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17966 p hg
    simpa only [d259, d3531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d259, d3531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d259, d3531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17968 (p : Pattern) (guard : d5268 p = 1) : d260 p ≤ (0 : Int) + d3532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d260, d3532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17964 p hg
    simpa only [d260, d3532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d260, d3532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17967 p hg
    simpa only [d260, d3532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17969 (p : Pattern) (guard : d5268 p = 1) : d261 p ≤ (0 : Int) + d3533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d261, d3533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17968 p hg
    simpa only [d261, d3533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d261, d3533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17957 p hg
    simpa only [d261, d3533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17970 (p : Pattern) (guard : d5268 p = 1) : d262 p ≤ (0 : Int) + d3534 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d262, d3534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17969 p hg
    simpa only [d262, d3534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d262, d3534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d262, d3534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17971 (p : Pattern) (guard : d5268 p = 1) : d263 p ≤ (0 : Int) + d3535 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d263, d3535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d263, d3535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d263, d3535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17970 p hg
    simpa only [d263, d3535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17972 (p : Pattern) (guard : d5268 p = 1) : d264 p ≤ (0 : Int) + d3536 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d264, d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17933 p hg
    simpa only [d264, d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d264, d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17971 p hg
    simpa only [d264, d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17973 (p : Pattern) (guard : d5268 p = 1) : d265 p ≤ (0 : Int) + d3537 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d265, d3537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17762 p hg
    simpa only [d265, d3537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d265, d3537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17972 p hg
    simpa only [d265, d3537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17974 (p : Pattern) (guard : d5268 p = 1) : d266 p ≤ (0 : Int) + d3538 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d266, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17916 p hg
    simpa only [d266, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d266, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17973 p hg
    simpa only [d266, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17975 (p : Pattern) (guard : d5268 p = 1) : d267 p ≤ (0 : Int) + d3539 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d267, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17875 p hg
    simpa only [d267, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d267, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17974 p hg
    simpa only [d267, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17976 (p : Pattern) (guard : d0 p = 1) : d318 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17977 (p : Pattern) (guard : d4902 p = 1) : d2184 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17976 p hg
    simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17978 (p : Pattern) (guard : d4902 p = 1) : d2185 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5657 p hg
    simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17979 (p : Pattern) (guard : d4902 p = 1) : d2186 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17980 (p : Pattern) (guard : d4902 p = 1) : d2187 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2187, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2187, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2187, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2187, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17981 (p : Pattern) (guard : d4902 p = 1) : d2188 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2188, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17979 p hg
    simpa only [d2188, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2188, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17980 p hg
    simpa only [d2188, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17982 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17983 (p : Pattern) (guard : d4902 p = 1) : d2189 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17982 p hg
    simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17984 (p : Pattern) (guard : d4902 p = 1) : d2190 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17983 p hg
    simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17985 (p : Pattern) (guard : d4902 p = 1) : d2191 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2191, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17984 p hg
    simpa only [d2191, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2191, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17980 p hg
    simpa only [d2191, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17986 (p : Pattern) (guard : d4902 p = 1) : d2192 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17981 p hg
    simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17985 p hg
    simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17987 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17988 (p : Pattern) (guard : d4902 p = 1) : d2193 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17987 p hg
    simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17989 (p : Pattern) (guard : d4902 p = 1) : d2194 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17988 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17990 (p : Pattern) (guard : d4902 p = 1) : d2195 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2195, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17989 p hg
    simpa only [d2195, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2195, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17980 p hg
    simpa only [d2195, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17991 (p : Pattern) (guard : d4902 p = 1) : d2196 p ≤ (0 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5661 p hg
    simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17992 (p : Pattern) (guard : d4902 p = 1) : d2197 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2197, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17991 p hg
    simpa only [d2197, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2197, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2197, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17993 (p : Pattern) (guard : d4902 p = 1) : d2198 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2198, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17991 p hg
    simpa only [d2198, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2198, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17992 p hg
    simpa only [d2198, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17994 (p : Pattern) (guard : d4902 p = 1) : d2199 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2199, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17990 p hg
    simpa only [d2199, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2199, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17993 p hg
    simpa only [d2199, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17995 (p : Pattern) (guard : d4902 p = 1) : d2200 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2200, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17986 p hg
    simpa only [d2200, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2200, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17994 p hg
    simpa only [d2200, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17996 (p : Pattern) (guard : d4902 p = 1) : d2201 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2201, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2201, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2201, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17980 p hg
    simpa only [d2201, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17997 (p : Pattern) (guard : d4902 p = 1) : d2202 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2202, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17996 p hg
    simpa only [d2202, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2202, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17993 p hg
    simpa only [d2202, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17998 (p : Pattern) (guard : d4902 p = 1) : d2203 p ≤ (0 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17999 (p : Pattern) (guard : d4902 p = 1) : d2204 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2204, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17998 p hg
    simpa only [d2204, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2204, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2204, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18000 (p : Pattern) (guard : d4902 p = 1) : d2205 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2205, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17998 p hg
    simpa only [d2205, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2205, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17999 p hg
    simpa only [d2205, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18001 (p : Pattern) (guard : d4902 p = 1) : d2206 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2206, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18000 p hg
    simpa only [d2206, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2206, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2206, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18002 (p : Pattern) (guard : d4902 p = 1) : d2207 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2207, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17997 p hg
    simpa only [d2207, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2207, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18001 p hg
    simpa only [d2207, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18003 (p : Pattern) (guard : d4902 p = 1) : d2208 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2208, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17995 p hg
    simpa only [d2208, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2208, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18002 p hg
    simpa only [d2208, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18004 (p : Pattern) (guard : d4902 p = 1) : d2209 p ≤ (0 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5677 p hg
    simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18005 (p : Pattern) (guard : d4902 p = 1) : d2210 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2210, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18004 p hg
    simpa only [d2210, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2210, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2210, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18006 (p : Pattern) (guard : d4902 p = 1) : d2211 p ≤ (0 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2211, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2211, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2211, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18005 p hg
    simpa only [d2211, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18007 (p : Pattern) (guard : d4902 p = 1) : d2212 p ≤ (0 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5808 p hg
    simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18008 (p : Pattern) (guard : d4902 p = 1) : d2213 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2213, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18007 p hg
    simpa only [d2213, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2213, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2213, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18009 (p : Pattern) (guard : d4902 p = 1) : d2214 p ≤ (0 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2214, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2214, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2214, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18008 p hg
    simpa only [d2214, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18010 (p : Pattern) (guard : d4902 p = 1) : d2215 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2215, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18006 p hg
    simpa only [d2215, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2215, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18009 p hg
    simpa only [d2215, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18011 (p : Pattern) (guard : d4902 p = 1) : d2216 p ≤ (0 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18012 (p : Pattern) (guard : d4902 p = 1) : d2217 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2217, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18011 p hg
    simpa only [d2217, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2217, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2217, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18013 (p : Pattern) (guard : d4902 p = 1) : d2218 p ≤ (0 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2218, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2218, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2218, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18012 p hg
    simpa only [d2218, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18014 (p : Pattern) (guard : d4902 p = 1) : d2219 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2219, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17991 p hg
    simpa only [d2219, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2219, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2219, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18015 (p : Pattern) (guard : d4902 p = 1) : d2220 p ≤ (0 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2220, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18013 p hg
    simpa only [d2220, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2220, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18014 p hg
    simpa only [d2220, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18016 (p : Pattern) (guard : d4902 p = 1) : d2221 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2221, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18010 p hg
    simpa only [d2221, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2221, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18015 p hg
    simpa only [d2221, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18017 (p : Pattern) (guard : d4902 p = 1) : d2222 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2222, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2222, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2222, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2222, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18018 (p : Pattern) (guard : d4902 p = 1) : d2223 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2223, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18017 p hg
    simpa only [d2223, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2223, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18014 p hg
    simpa only [d2223, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18019 (p : Pattern) (guard : d4902 p = 1) : d2224 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2224, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17998 p hg
    simpa only [d2224, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2224, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2224, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18020 (p : Pattern) (guard : d4902 p = 1) : d2225 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2225, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18019 p hg
    simpa only [d2225, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2225, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2225, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18021 (p : Pattern) (guard : d4902 p = 1) : d2226 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2226, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18018 p hg
    simpa only [d2226, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2226, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18020 p hg
    simpa only [d2226, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18022 (p : Pattern) (guard : d4902 p = 1) : d2227 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2227, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18016 p hg
    simpa only [d2227, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2227, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18021 p hg
    simpa only [d2227, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18023 (p : Pattern) (guard : d4902 p = 1) : d2228 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2228, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18003 p hg
    simpa only [d2228, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2228, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18022 p hg
    simpa only [d2228, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18024 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18025 (p : Pattern) (guard : d4902 p = 1) : d2229 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18024 p hg
    simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18026 (p : Pattern) (guard : d4902 p = 1) : d2230 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18025 p hg
    simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18027 (p : Pattern) (guard : d4902 p = 1) : d2231 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2231, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18026 p hg
    simpa only [d2231, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2231, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17980 p hg
    simpa only [d2231, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18028 (p : Pattern) (guard : d4902 p = 1) : d2232 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2232, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18004 p hg
    simpa only [d2232, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2232, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18005 p hg
    simpa only [d2232, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18029 (p : Pattern) (guard : d4902 p = 1) : d2233 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2233, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18027 p hg
    simpa only [d2233, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2233, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d2233, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18030 (p : Pattern) (guard : d4902 p = 1) : d2234 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2234, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17993 p hg
    simpa only [d2234, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2234, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18000 p hg
    simpa only [d2234, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18031 (p : Pattern) (guard : d4902 p = 1) : d2235 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2235, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18029 p hg
    simpa only [d2235, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2235, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18030 p hg
    simpa only [d2235, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18032 (p : Pattern) (guard : d4902 p = 1) : d2236 p ≤ (0 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18033 (p : Pattern) (guard : d4902 p = 1) : d2237 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2237, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18032 p hg
    simpa only [d2237, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2237, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2237, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18034 (p : Pattern) (guard : d4902 p = 1) : d2238 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2238, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18032 p hg
    simpa only [d2238, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2238, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18033 p hg
    simpa only [d2238, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18035 (p : Pattern) (guard : d4902 p = 1) : d2239 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2239, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17993 p hg
    simpa only [d2239, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2239, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18034 p hg
    simpa only [d2239, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18036 (p : Pattern) (guard : d4902 p = 1) : d2240 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2240, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18011 p hg
    simpa only [d2240, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2240, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18012 p hg
    simpa only [d2240, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18037 (p : Pattern) (guard : d4902 p = 1) : d2241 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2241, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18036 p hg
    simpa only [d2241, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2241, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2241, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18038 (p : Pattern) (guard : d4902 p = 1) : d2242 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2242, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18035 p hg
    simpa only [d2242, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2242, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18037 p hg
    simpa only [d2242, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18039 (p : Pattern) (guard : d4902 p = 1) : d2243 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2243, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18031 p hg
    simpa only [d2243, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2243, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18038 p hg
    simpa only [d2243, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18040 (p : Pattern) (guard : d4902 p = 1) : d2244 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2244, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18004 p hg
    simpa only [d2244, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2244, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2244, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18041 (p : Pattern) (guard : d4902 p = 1) : d2245 p ≤ (0 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2245, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18009 p hg
    simpa only [d2245, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2245, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18040 p hg
    simpa only [d2245, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18042 (p : Pattern) (guard : d4902 p = 1) : d2246 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2246, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18014 p hg
    simpa only [d2246, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2246, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18019 p hg
    simpa only [d2246, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18043 (p : Pattern) (guard : d4902 p = 1) : d2247 p ≤ (0 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2247, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18041 p hg
    simpa only [d2247, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2247, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18042 p hg
    simpa only [d2247, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18044 (p : Pattern) (guard : d4902 p = 1) : d2248 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2248, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18032 p hg
    simpa only [d2248, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2248, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2248, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18045 (p : Pattern) (guard : d4902 p = 1) : d2249 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2249, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18014 p hg
    simpa only [d2249, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2249, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18044 p hg
    simpa only [d2249, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18046 (p : Pattern) (guard : d4902 p = 1) : d2250 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2250, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18011 p hg
    simpa only [d2250, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2250, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2250, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18047 (p : Pattern) (guard : d4902 p = 1) : d2251 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2251, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18046 p hg
    simpa only [d2251, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2251, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2251, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18048 (p : Pattern) (guard : d4902 p = 1) : d2252 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2252, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18045 p hg
    simpa only [d2252, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2252, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18047 p hg
    simpa only [d2252, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18049 (p : Pattern) (guard : d4902 p = 1) : d2253 p ≤ (0 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2253, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18043 p hg
    simpa only [d2253, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2253, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18048 p hg
    simpa only [d2253, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18050 (p : Pattern) (guard : d4902 p = 1) : d2254 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2254, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18039 p hg
    simpa only [d2254, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2254, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18049 p hg
    simpa only [d2254, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18051 (p : Pattern) (guard : d4902 p = 1) : d2255 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2255, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18023 p hg
    simpa only [d2255, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2255, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18050 p hg
    simpa only [d2255, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18052 (p : Pattern) (guard : d4902 p = 1) : d2256 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2256, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17996 p hg
    simpa only [d2256, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2256, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17997 p hg
    simpa only [d2256, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18053 (p : Pattern) (guard : d4902 p = 1) : d2257 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2257, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18052 p hg
    simpa only [d2257, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2257, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18002 p hg
    simpa only [d2257, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18054 (p : Pattern) (guard : d4902 p = 1) : d2258 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2258, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18007 p hg
    simpa only [d2258, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2258, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18008 p hg
    simpa only [d2258, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18055 (p : Pattern) (guard : d4902 p = 1) : d2259 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2259, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d2259, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2259, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18054 p hg
    simpa only [d2259, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18056 (p : Pattern) (guard : d4902 p = 1) : d2260 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2260, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18055 p hg
    simpa only [d2260, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2260, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18037 p hg
    simpa only [d2260, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18057 (p : Pattern) (guard : d4902 p = 1) : d2261 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2261, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18056 p hg
    simpa only [d2261, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2261, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2261, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18058 (p : Pattern) (guard : d4902 p = 1) : d2262 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2262, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18053 p hg
    simpa only [d2262, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2262, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18057 p hg
    simpa only [d2262, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18059 (p : Pattern) (guard : d4902 p = 1) : d2263 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2263, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17996 p hg
    simpa only [d2263, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2263, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d2263, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
