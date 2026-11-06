/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons222
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31220 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d5 p := by
  change (12 : Int) ≤ (9 : Int) + 5
  decide
theorem compare31221 (p : Pattern) (guard : d6326 p = 1) : d348 p ≤ (9 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31148 p hg
    simpa only [d6326, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31220 p hg
    simpa only [d6326, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31222 (p : Pattern) (guard : d6326 p = 1) : d3784 p ≤ (9 : Int) + d5 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31155 p hg
    simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31221 p hg
    simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31223 (p : Pattern) (guard : d6326 p = 1) : d3785 p ≤ (9 : Int) + d5 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31219 p hg
    simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31222 p hg
    simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31224 (p : Pattern) (guard : d6326 p = 1) : d3786 p ≤ (9 : Int) + d5 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31152 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31223 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31225 (p : Pattern) (guard : d6326 p = 1) : d3787 p ≤ (9 : Int) + d6417 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3787, d6417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31224 p hg
    simpa only [d3787, d6417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3787, d6417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3787, d6417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31226 (p : Pattern) (guard : d6326 p = 1) : d3788 p ≤ (9 : Int) + d6418 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3788, d6418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31215 p hg
    simpa only [d3788, d6418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3788, d6418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31225 p hg
    simpa only [d3788, d6418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31227 (p : Pattern) (guard : d6326 p = 1) : d3789 p ≤ (9 : Int) + d6419 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3789, d6419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31214 p hg
    simpa only [d3789, d6419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3789, d6419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31226 p hg
    simpa only [d3789, d6419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31228 (p : Pattern) (guard : d6326 p = 1) : d3790 p ≤ (9 : Int) + d6420 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3790, d6420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31035 p hg
    simpa only [d3790, d6420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3790, d6420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3790, d6420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31229 (p : Pattern) (guard : d6326 p = 1) : d3791 p ≤ (9 : Int) + d6421 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3791, d6421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31226 p hg
    simpa only [d3791, d6421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3791, d6421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31228 p hg
    simpa only [d3791, d6421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31230 (p : Pattern) (guard : d6326 p = 1) : d3792 p ≤ (9 : Int) + d6422 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3792, d6422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31227 p hg
    simpa only [d3792, d6422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3792, d6422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31229 p hg
    simpa only [d3792, d6422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31231 (p : Pattern) (guard : d6326 p = 1) : d3793 p ≤ (9 : Int) + d6423 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3793, d6423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31170 p hg
    simpa only [d3793, d6423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3793, d6423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31230 p hg
    simpa only [d3793, d6423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31232 (p : Pattern) (guard : d6326 p = 1) : d3794 p ≤ (9 : Int) + d3 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31185 p hg
    simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31192 p hg
    simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31233 (p : Pattern) (guard : d6326 p = 1) : d3795 p ≤ (9 : Int) + d3 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31232 p hg
    simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31192 p hg
    simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31234 (p : Pattern) (guard : d6326 p = 1) : d3796 p ≤ (9 : Int) + d3 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31185 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31233 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31235 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (9 : Int) + d3 p := by
  change (5 : Int) ≤ (9 : Int) + 3
  decide
theorem compare31236 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (9 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31235 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31183 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31237 (p : Pattern) (guard : d6326 p = 1) : d3797 p ≤ (9 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31181 p hg
    simpa only [d6326, d3797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31236 p hg
    simpa only [d6326, d3797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31238 (p : Pattern) (guard : d6326 p = 1) : d3798 p ≤ (9 : Int) + d3 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31185 p hg
    simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31237 p hg
    simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31239 (p : Pattern) (guard : d6326 p = 1) : d3799 p ≤ (9 : Int) + d3 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31238 p hg
    simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31237 p hg
    simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31240 (p : Pattern) (guard : d6326 p = 1) : d3800 p ≤ (9 : Int) + d6411 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3800, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31239 p hg
    simpa only [d3800, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3800, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3800, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31241 (p : Pattern) (guard : d6326 p = 1) : d3801 p ≤ (9 : Int) + d6424 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3801, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31234 p hg
    simpa only [d3801, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3801, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31240 p hg
    simpa only [d3801, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31242 (p : Pattern) (guard : d6326 p = 1) : d3802 p ≤ (9 : Int) + d6425 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3802, d6425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31146 p hg
    simpa only [d3802, d6425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3802, d6425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31241 p hg
    simpa only [d3802, d6425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31243 (p : Pattern) (guard : d6326 p = 1) : d3803 p ≤ (9 : Int) + d6426 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3803, d6426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31165 p hg
    simpa only [d3803, d6426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3803, d6426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31023 p hg
    simpa only [d3803, d6426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31244 (p : Pattern) (guard : d6326 p = 1) : d3804 p ≤ (9 : Int) + d6427 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3804, d6427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31242 p hg
    simpa only [d3804, d6427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3804, d6427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31243 p hg
    simpa only [d3804, d6427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31245 (p : Pattern) (guard : d6326 p = 1) : d3805 p ≤ (9 : Int) + d6428 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3805, d6428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31165 p hg
    simpa only [d3805, d6428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3805, d6428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31026 p hg
    simpa only [d3805, d6428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31246 (p : Pattern) (guard : d6326 p = 1) : d3806 p ≤ (9 : Int) + d6429 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3806, d6429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31245 p hg
    simpa only [d3806, d6429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3806, d6429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3806, d6429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31247 (p : Pattern) (guard : d6326 p = 1) : d3807 p ≤ (9 : Int) + d6430 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3807, d6430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31244 p hg
    simpa only [d3807, d6430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3807, d6430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31246 p hg
    simpa only [d3807, d6430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31248 (p : Pattern) (guard : d6326 p = 1) : d3808 p ≤ (9 : Int) + d3 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31185 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31196 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31249 (p : Pattern) (guard : d6326 p = 1) : d3809 p ≤ (9 : Int) + d6431 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3809, d6431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31248 p hg
    simpa only [d3809, d6431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3809, d6431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3809, d6431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31250 (p : Pattern) (guard : d6326 p = 1) : d3810 p ≤ (9 : Int) + d6432 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3810, d6432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31213 p hg
    simpa only [d3810, d6432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3810, d6432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31249 p hg
    simpa only [d3810, d6432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31251 (p : Pattern) (guard : d6326 p = 1) : d3811 p ≤ (9 : Int) + d6433 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3811, d6433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31225 p hg
    simpa only [d3811, d6433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3811, d6433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31035 p hg
    simpa only [d3811, d6433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31252 (p : Pattern) (guard : d6326 p = 1) : d3812 p ≤ (9 : Int) + d6434 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3812, d6434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31250 p hg
    simpa only [d3812, d6434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3812, d6434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31251 p hg
    simpa only [d3812, d6434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31253 (p : Pattern) (guard : d6326 p = 1) : d3813 p ≤ (9 : Int) + d6435 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3813, d6435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31225 p hg
    simpa only [d3813, d6435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3813, d6435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31037 p hg
    simpa only [d3813, d6435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31254 (p : Pattern) (guard : d6326 p = 1) : d3814 p ≤ (9 : Int) + d6436 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3814, d6436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31253 p hg
    simpa only [d3814, d6436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3814, d6436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3814, d6436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31255 (p : Pattern) (guard : d6326 p = 1) : d3815 p ≤ (9 : Int) + d6437 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3815, d6437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31252 p hg
    simpa only [d3815, d6437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3815, d6437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31254 p hg
    simpa only [d3815, d6437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31256 (p : Pattern) (guard : d6326 p = 1) : d3816 p ≤ (9 : Int) + d6438 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3816, d6438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31247 p hg
    simpa only [d3816, d6438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3816, d6438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31255 p hg
    simpa only [d3816, d6438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31257 (p : Pattern) (guard : d6326 p = 1) : d3817 p ≤ (9 : Int) + d6439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3817, d6439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31231 p hg
    simpa only [d3817, d6439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3817, d6439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31256 p hg
    simpa only [d3817, d6439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31258 (p : Pattern) (guard : d6326 p = 1) : d3818 p ≤ (9 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31134 p hg
    simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31173 p hg
    simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31259 (p : Pattern) (guard : d6326 p = 1) : d3819 p ≤ (9 : Int) + d1 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31174 p hg
    simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31258 p hg
    simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31260 (p : Pattern) (guard : d6326 p = 1) : d3820 p ≤ (9 : Int) + d1 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31259 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31261 (p : Pattern) (guard : d6326 p = 1) : d3821 p ≤ (9 : Int) + d6402 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3821, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31136 p hg
    simpa only [d3821, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3821, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3821, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31262 (p : Pattern) (guard : d6326 p = 1) : d3822 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3822, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31260 p hg
    simpa only [d3822, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3822, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31261 p hg
    simpa only [d3822, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31263 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (9 : Int) + d1 p := by
  change (9 : Int) ≤ (9 : Int) + 1
  decide
theorem compare31264 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (9 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31263 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31125 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31265 (p : Pattern) (guard : d6326 p = 1) : d3823 p ≤ (9 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31128 p hg
    simpa only [d6326, d3823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31264 p hg
    simpa only [d6326, d3823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31266 (p : Pattern) (guard : d6326 p = 1) : d3824 p ≤ (9 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31134 p hg
    simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31265 p hg
    simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31267 (p : Pattern) (guard : d6326 p = 1) : d3825 p ≤ (9 : Int) + d1 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31174 p hg
    simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31266 p hg
    simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31268 (p : Pattern) (guard : d6326 p = 1) : d3826 p ≤ (9 : Int) + d6402 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3826, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31267 p hg
    simpa only [d3826, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3826, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3826, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31269 (p : Pattern) (guard : d6326 p = 1) : d3827 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3827, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31180 p hg
    simpa only [d3827, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3827, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31268 p hg
    simpa only [d3827, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31270 (p : Pattern) (guard : d6326 p = 1) : d3828 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31262 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31269 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31271 (p : Pattern) (guard : d6326 p = 1) : d3829 p ≤ (9 : Int) + d6402 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3829, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31179 p hg
    simpa only [d3829, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3829, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3829, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31272 (p : Pattern) (guard : d6326 p = 1) : d3830 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3830, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31180 p hg
    simpa only [d3830, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3830, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31271 p hg
    simpa only [d3830, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31273 (p : Pattern) (guard : d6326 p = 1) : d3831 p ≤ (9 : Int) + d6404 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3831, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31223 p hg
    simpa only [d3831, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3831, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3831, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31274 (p : Pattern) (guard : d6326 p = 1) : d3832 p ≤ (9 : Int) + d6405 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3832, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31224 p hg
    simpa only [d3832, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3832, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31273 p hg
    simpa only [d3832, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31275 (p : Pattern) (guard : d6326 p = 1) : d3833 p ≤ (9 : Int) + d6406 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3833, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31272 p hg
    simpa only [d3833, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3833, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31274 p hg
    simpa only [d3833, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31276 (p : Pattern) (guard : d6326 p = 1) : d3834 p ≤ (9 : Int) + d6407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3834, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31270 p hg
    simpa only [d3834, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3834, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31275 p hg
    simpa only [d3834, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31277 (p : Pattern) (guard : d6326 p = 1) : d3835 p ≤ (9 : Int) + d6409 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3835, d6409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31275 p hg
    simpa only [d3835, d6409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3835, d6409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31168 p hg
    simpa only [d3835, d6409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31278 (p : Pattern) (guard : d6326 p = 1) : d3836 p ≤ (9 : Int) + d6410 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3836, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31276 p hg
    simpa only [d3836, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3836, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31277 p hg
    simpa only [d3836, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31279 (p : Pattern) (guard : d6326 p = 1) : d3837 p ≤ (9 : Int) + d6424 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3837, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31248 p hg
    simpa only [d3837, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3837, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31197 p hg
    simpa only [d3837, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31280 (p : Pattern) (guard : d6326 p = 1) : d3838 p ≤ (9 : Int) + d7 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31203 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31211 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31281 (p : Pattern) (guard : d6326 p = 1) : d3839 p ≤ (9 : Int) + d6440 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3839, d6440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31280 p hg
    simpa only [d3839, d6440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3839, d6440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31212 p hg
    simpa only [d3839, d6440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31282 (p : Pattern) (guard : d6326 p = 1) : d3840 p ≤ (9 : Int) + d6441 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3840, d6441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31279 p hg
    simpa only [d3840, d6441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3840, d6441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31281 p hg
    simpa only [d3840, d6441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31283 (p : Pattern) (guard : d6326 p = 1) : d3841 p ≤ (9 : Int) + d6442 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3841, d6442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31282 p hg
    simpa only [d3841, d6442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3841, d6442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3841, d6442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31284 (p : Pattern) (guard : d6326 p = 1) : d3842 p ≤ (9 : Int) + d6443 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3842, d6443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31283 p hg
    simpa only [d3842, d6443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3842, d6443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3842, d6443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31285 (p : Pattern) (guard : d6326 p = 1) : d3843 p ≤ (9 : Int) + d6444 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3843, d6444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31278 p hg
    simpa only [d3843, d6444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3843, d6444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31284 p hg
    simpa only [d3843, d6444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31286 (p : Pattern) (guard : d6326 p = 1) : d3844 p ≤ (9 : Int) + d6425 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3844, d6425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31269 p hg
    simpa only [d3844, d6425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3844, d6425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31279 p hg
    simpa only [d3844, d6425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31287 (p : Pattern) (guard : d6326 p = 1) : d3845 p ≤ (9 : Int) + d6426 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3845, d6426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31274 p hg
    simpa only [d3845, d6426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3845, d6426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31023 p hg
    simpa only [d3845, d6426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31288 (p : Pattern) (guard : d6326 p = 1) : d3846 p ≤ (9 : Int) + d6427 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3846, d6427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31286 p hg
    simpa only [d3846, d6427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3846, d6427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31287 p hg
    simpa only [d3846, d6427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31289 (p : Pattern) (guard : d6326 p = 1) : d3847 p ≤ (9 : Int) + d6428 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3847, d6428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31274 p hg
    simpa only [d3847, d6428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3847, d6428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31026 p hg
    simpa only [d3847, d6428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31290 (p : Pattern) (guard : d6326 p = 1) : d3848 p ≤ (9 : Int) + d6429 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3848, d6429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31289 p hg
    simpa only [d3848, d6429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3848, d6429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3848, d6429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31291 (p : Pattern) (guard : d6326 p = 1) : d3849 p ≤ (9 : Int) + d6430 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3849, d6430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31288 p hg
    simpa only [d3849, d6430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3849, d6430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31290 p hg
    simpa only [d3849, d6430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31292 (p : Pattern) (guard : d6326 p = 1) : d3850 p ≤ (9 : Int) + d6445 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3850, d6445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31281 p hg
    simpa only [d3850, d6445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3850, d6445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3850, d6445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31293 (p : Pattern) (guard : d6326 p = 1) : d3851 p ≤ (9 : Int) + d6446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3851, d6446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31292 p hg
    simpa only [d3851, d6446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3851, d6446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3851, d6446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31294 (p : Pattern) (guard : d6326 p = 1) : d3852 p ≤ (9 : Int) + d6447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3852, d6447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31293 p hg
    simpa only [d3852, d6447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3852, d6447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3852, d6447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31295 (p : Pattern) (guard : d6326 p = 1) : d3853 p ≤ (9 : Int) + d6448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3853, d6448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31291 p hg
    simpa only [d3853, d6448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3853, d6448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31294 p hg
    simpa only [d3853, d6448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31296 (p : Pattern) (guard : d6326 p = 1) : d3854 p ≤ (9 : Int) + d6449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3854, d6449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31285 p hg
    simpa only [d3854, d6449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3854, d6449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31295 p hg
    simpa only [d3854, d6449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31297 (p : Pattern) (guard : d6326 p = 1) : d3855 p ≤ (9 : Int) + d6450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3855, d6450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31257 p hg
    simpa only [d3855, d6450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3855, d6450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31296 p hg
    simpa only [d3855, d6450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31298 (p : Pattern) (guard : d6326 p = 1) : d3856 p ≤ (9 : Int) + d6451 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3856, d6451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31168 p hg
    simpa only [d3856, d6451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3856, d6451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3856, d6451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31299 (p : Pattern) (guard : d6326 p = 1) : d3857 p ≤ (9 : Int) + d6452 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3857, d6452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31298 p hg
    simpa only [d3857, d6452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3857, d6452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3857, d6452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31300 (p : Pattern) (guard : d6326 p = 1) : d3858 p ≤ (9 : Int) + d6453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3858, d6453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31299 p hg
    simpa only [d3858, d6453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3858, d6453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3858, d6453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31301 (p : Pattern) (guard : d6326 p = 1) : d3859 p ≤ (9 : Int) + d6454 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3859, d6454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31300 p hg
    simpa only [d3859, d6454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3859, d6454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3859, d6454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31302 (p : Pattern) (guard : d6326 p = 1) : d3860 p ≤ (9 : Int) + d6455 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3860, d6455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31296 p hg
    simpa only [d3860, d6455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3860, d6455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31301 p hg
    simpa only [d3860, d6455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31303 (p : Pattern) (guard : d6326 p = 1) : d3861 p ≤ (9 : Int) + d6456 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3861, d6456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31297 p hg
    simpa only [d3861, d6456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3861, d6456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31302 p hg
    simpa only [d3861, d6456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31304 (p : Pattern) (guard : d6326 p = 1) : d3862 p ≤ (9 : Int) + d6407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3862, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31146 p hg
    simpa only [d3862, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3862, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31166 p hg
    simpa only [d3862, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31305 (p : Pattern) (guard : d6326 p = 1) : d3863 p ≤ (9 : Int) + d6410 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3863, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31304 p hg
    simpa only [d3863, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3863, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31169 p hg
    simpa only [d3863, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31306 (p : Pattern) (guard : d6326 p = 1) : d3864 p ≤ (9 : Int) + d6423 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3864, d6423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31305 p hg
    simpa only [d3864, d6423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3864, d6423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31230 p hg
    simpa only [d3864, d6423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31307 (p : Pattern) (guard : d6326 p = 1) : d3865 p ≤ (9 : Int) + d6439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3865, d6439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31306 p hg
    simpa only [d3865, d6439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3865, d6439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31256 p hg
    simpa only [d3865, d6439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31308 (p : Pattern) (guard : d6326 p = 1) : d3866 p ≤ (9 : Int) + d6450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3866, d6450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31307 p hg
    simpa only [d3866, d6450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3866, d6450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31296 p hg
    simpa only [d3866, d6450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31309 (p : Pattern) (guard : d6326 p = 1) : d3867 p ≤ (9 : Int) + d6457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3867, d6457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31296 p hg
    simpa only [d3867, d6457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3867, d6457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3867, d6457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31310 (p : Pattern) (guard : d6326 p = 1) : d3868 p ≤ (9 : Int) + d6458 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3868, d6458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31308 p hg
    simpa only [d3868, d6458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3868, d6458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31309 p hg
    simpa only [d3868, d6458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31311 (p : Pattern) (guard : d6326 p = 1) : d3869 p ≤ (9 : Int) + d6459 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3869, d6459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31303 p hg
    simpa only [d3869, d6459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3869, d6459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31310 p hg
    simpa only [d3869, d6459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31312 (p : Pattern) (guard : d6326 p = 1) : d3870 p ≤ (9 : Int) + d6460 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3870, d6460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31107 p hg
    simpa only [d3870, d6460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3870, d6460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31311 p hg
    simpa only [d3870, d6460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31313 (p : Pattern) (guard : d6326 p = 1) : d3871 p ≤ (9 : Int) + d6461 p := by
  cases selected : p 49 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3871, d6461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31122 p hg
    simpa only [d3871, d6461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3871, d6461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31312 p hg
    simpa only [d3871, d6461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31314 (p : Pattern) (guard : d6326 p = 1) : d3872 p ≤ (9 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30885 p hg
    simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30976 p hg
    simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31315 (p : Pattern) (guard : d6326 p = 1) : d3873 p ≤ (9 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30977 p hg
    simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31314 p hg
    simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31316 (p : Pattern) (guard : d6326 p = 1) : d3874 p ≤ (9 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30882 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31315 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31317 (p : Pattern) (guard : d6326 p = 1) : d3875 p ≤ (9 : Int) + d6329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3875, d6329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d3875, d6329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3875, d6329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3875, d6329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31318 (p : Pattern) (guard : d6326 p = 1) : d3876 p ≤ (9 : Int) + d6330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3876, d6330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31316 p hg
    simpa only [d3876, d6330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3876, d6330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31317 p hg
    simpa only [d3876, d6330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31319 (p : Pattern) (guard : d6326 p = 1) : d3877 p ≤ (9 : Int) + d6331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3877, d6331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31047 p hg
    simpa only [d3877, d6331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3877, d6331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31318 p hg
    simpa only [d3877, d6331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31320 (p : Pattern) (guard : d6326 p = 1) : d3878 p ≤ (9 : Int) + d6332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3878, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31047 p hg
    simpa only [d3878, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3878, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31319 p hg
    simpa only [d3878, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31321 (p : Pattern) (guard : d6326 p = 1) : d3879 p ≤ (9 : Int) + d6336 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3879, d6336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31319 p hg
    simpa only [d3879, d6336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3879, d6336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31064 p hg
    simpa only [d3879, d6336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31322 (p : Pattern) (guard : d6326 p = 1) : d3880 p ≤ (9 : Int) + d6337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3880, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31320 p hg
    simpa only [d3880, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3880, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31321 p hg
    simpa only [d3880, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31323 (p : Pattern) (guard : d6326 p = 1) : d3881 p ≤ (9 : Int) + d6462 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3881, d6462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31030 p hg
    simpa only [d3881, d6462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3881, d6462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30960 p hg
    simpa only [d3881, d6462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31324 (p : Pattern) (guard : d6326 p = 1) : d3882 p ≤ (9 : Int) + d6463 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3882, d6463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31067 p hg
    simpa only [d3882, d6463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3882, d6463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31323 p hg
    simpa only [d3882, d6463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31325 (p : Pattern) (guard : d6326 p = 1) : d3883 p ≤ (9 : Int) + d6464 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3883, d6464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31030 p hg
    simpa only [d3883, d6464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3883, d6464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30972 p hg
    simpa only [d3883, d6464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31326 (p : Pattern) (guard : d6326 p = 1) : d3884 p ≤ (9 : Int) + d6465 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3884, d6465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31068 p hg
    simpa only [d3884, d6465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3884, d6465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3884, d6465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31327 (p : Pattern) (guard : d6326 p = 1) : d3885 p ≤ (9 : Int) + d6466 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3885, d6466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31325 p hg
    simpa only [d3885, d6466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3885, d6466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31326 p hg
    simpa only [d3885, d6466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31328 (p : Pattern) (guard : d6326 p = 1) : d3886 p ≤ (9 : Int) + d6467 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3886, d6467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31324 p hg
    simpa only [d3886, d6467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3886, d6467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31327 p hg
    simpa only [d3886, d6467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31329 (p : Pattern) (guard : d6326 p = 1) : d3887 p ≤ (9 : Int) + d6468 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3887, d6468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31031 p hg
    simpa only [d3887, d6468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3887, d6468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31326 p hg
    simpa only [d3887, d6468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31330 (p : Pattern) (guard : d6326 p = 1) : d3888 p ≤ (9 : Int) + d6469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3888, d6469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31329 p hg
    simpa only [d3888, d6469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3888, d6469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31038 p hg
    simpa only [d3888, d6469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31331 (p : Pattern) (guard : d6326 p = 1) : d3889 p ≤ (9 : Int) + d6470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3889, d6470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31328 p hg
    simpa only [d3889, d6470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3889, d6470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31330 p hg
    simpa only [d3889, d6470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31332 (p : Pattern) (guard : d6326 p = 1) : d3890 p ≤ (9 : Int) + d6471 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3890, d6471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31322 p hg
    simpa only [d3890, d6471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3890, d6471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31331 p hg
    simpa only [d3890, d6471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31333 (p : Pattern) (guard : d6326 p = 1) : d3891 p ≤ (9 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30939 p hg
    simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30935 p hg
    simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31334 (p : Pattern) (guard : d6326 p = 1) : d3892 p ≤ (9 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31333 p hg
    simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31335 (p : Pattern) (guard : d6326 p = 1) : d3893 p ≤ (9 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30932 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31334 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31336 (p : Pattern) (guard : d6326 p = 1) : d3894 p ≤ (9 : Int) + d6338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3894, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31000 p hg
    simpa only [d3894, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3894, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3894, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31337 (p : Pattern) (guard : d6326 p = 1) : d3895 p ≤ (9 : Int) + d6355 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3895, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31335 p hg
    simpa only [d3895, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3895, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31336 p hg
    simpa only [d3895, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31338 (p : Pattern) (guard : d6326 p = 1) : d3896 p ≤ (9 : Int) + d6356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3896, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31047 p hg
    simpa only [d3896, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3896, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31337 p hg
    simpa only [d3896, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31339 (p : Pattern) (guard : d6326 p = 1) : d3897 p ≤ (9 : Int) + d6357 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3897, d6357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31318 p hg
    simpa only [d3897, d6357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3897, d6357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31063 p hg
    simpa only [d3897, d6357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31340 (p : Pattern) (guard : d6326 p = 1) : d3898 p ≤ (9 : Int) + d6358 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3898, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31338 p hg
    simpa only [d3898, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3898, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31339 p hg
    simpa only [d3898, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31341 (p : Pattern) (guard : d6326 p = 1) : d3899 p ≤ (9 : Int) + d6361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3899, d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31318 p hg
    simpa only [d3899, d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3899, d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31023 p hg
    simpa only [d3899, d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31342 (p : Pattern) (guard : d6326 p = 1) : d3900 p ≤ (9 : Int) + d6364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3900, d6364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31341 p hg
    simpa only [d3900, d6364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3900, d6364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31027 p hg
    simpa only [d3900, d6364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31343 (p : Pattern) (guard : d6326 p = 1) : d3901 p ≤ (9 : Int) + d6365 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3901, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31340 p hg
    simpa only [d3901, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3901, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31342 p hg
    simpa only [d3901, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31344 (p : Pattern) (guard : d6326 p = 1) : d3902 p ≤ (9 : Int) + d6472 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3902, d6472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31323 p hg
    simpa only [d3902, d6472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3902, d6472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30983 p hg
    simpa only [d3902, d6472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31345 (p : Pattern) (guard : d6326 p = 1) : d3903 p ≤ (9 : Int) + d6473 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3903, d6473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31326 p hg
    simpa only [d3903, d6473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3903, d6473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31037 p hg
    simpa only [d3903, d6473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31346 (p : Pattern) (guard : d6326 p = 1) : d3904 p ≤ (9 : Int) + d6474 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3904, d6474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31344 p hg
    simpa only [d3904, d6474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3904, d6474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31345 p hg
    simpa only [d3904, d6474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31347 (p : Pattern) (guard : d6326 p = 1) : d3905 p ≤ (9 : Int) + d6475 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3905, d6475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31326 p hg
    simpa only [d3905, d6475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3905, d6475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3905, d6475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31348 (p : Pattern) (guard : d6326 p = 1) : d3906 p ≤ (9 : Int) + d6476 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3906, d6476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31347 p hg
    simpa only [d3906, d6476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3906, d6476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3906, d6476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31349 (p : Pattern) (guard : d6326 p = 1) : d3907 p ≤ (9 : Int) + d6477 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3907, d6477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31346 p hg
    simpa only [d3907, d6477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3907, d6477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31348 p hg
    simpa only [d3907, d6477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31350 (p : Pattern) (guard : d6326 p = 1) : d3908 p ≤ (9 : Int) + d6478 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3908, d6478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31343 p hg
    simpa only [d3908, d6478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3908, d6478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31349 p hg
    simpa only [d3908, d6478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31351 (p : Pattern) (guard : d6326 p = 1) : d3909 p ≤ (9 : Int) + d6479 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3909, d6479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31332 p hg
    simpa only [d3909, d6479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3909, d6479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31350 p hg
    simpa only [d3909, d6479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31352 (p : Pattern) (guard : d6326 p = 1) : d3910 p ≤ (9 : Int) + d0 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31052 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31353 (p : Pattern) (guard : d6326 p = 1) : d3911 p ≤ (9 : Int) + d6327 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3911, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31044 p hg
    simpa only [d3911, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3911, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3911, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31354 (p : Pattern) (guard : d6326 p = 1) : d3912 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3912, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31352 p hg
    simpa only [d3912, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3912, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31353 p hg
    simpa only [d3912, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31355 (p : Pattern) (guard : d6326 p = 1) : d3913 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31354 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31057 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31356 (p : Pattern) (guard : d6326 p = 1) : d3914 p ≤ (9 : Int) + d6480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3914, d6480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31355 p hg
    simpa only [d3914, d6480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3914, d6480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31070 p hg
    simpa only [d3914, d6480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31357 (p : Pattern) (guard : d6326 p = 1) : d3915 p ≤ (9 : Int) + d6481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3915, d6481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31356 p hg
    simpa only [d3915, d6481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3915, d6481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31071 p hg
    simpa only [d3915, d6481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31358 (p : Pattern) (guard : d0 p = 1) : d190 p ≤ (9 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31359 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (9 : Int) + d8 p := by
  omega
end NetHack.Sokoban22Refined85
