import NetHack.Soko22Hazard87.Compare155
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39000 (p : Pattern) (guard : d317692 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317691 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38999 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39001 (p : Pattern) (guard : d317693 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317692 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39000 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39002 (p : Pattern) (guard : d317694 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317693 p = 1 := by simpa only [d317694, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39001 p hg
    simpa only [d317694, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317694, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d317694, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39003 (p : Pattern) (guard : d317695 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317694 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39002 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39004 (p : Pattern) (guard : d1531 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare39005 (p : Pattern) (guard : d1547 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39004 p hg
    simpa only [d1547, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d1547, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39006 (p : Pattern) (guard : d39244 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39005 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39007 (p : Pattern) (guard : d258107 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39006 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39008 (p : Pattern) (guard : d258108 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39007 p hg
    simpa only [d258108, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d258108, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39009 (p : Pattern) (guard : d316767 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38578 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39008 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39010 (p : Pattern) (guard : d317696 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317695 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39003 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316767 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39009 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39011 (p : Pattern) (guard : d317697 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317696 p = 1 := by simpa only [d317697, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39010 p hg
    simpa only [d317697, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317697, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d317697, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39012 (p : Pattern) (guard : d317698 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38997 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317697 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39011 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39013 (p : Pattern) (guard : d317699 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317698 p = 1 := by simpa only [d317699, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39012 p hg
    simpa only [d317699, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317699, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317699, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39014 (p : Pattern) (guard : d317700 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317699 p = 1 := by simpa only [d317700, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39013 p hg
    simpa only [d317700, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317700, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317700, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39015 (p : Pattern) (guard : d317701 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317701, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317701, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317700 p = 1 := by simpa only [d317701, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39014 p hg
    simpa only [d317701, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39016 (p : Pattern) (guard : d317702 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317701 p = 1 := by simpa only [d317702, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39015 p hg
    simpa only [d317702, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317702, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317702, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39017 (p : Pattern) (guard : d34366 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare39018 (p : Pattern) (guard : d34367 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d34366 p = 1 := by simpa only [d34367, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39017 p hg
    simpa only [d34367, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34367, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d34367, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39019 (p : Pattern) (guard : d316576 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34367 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39018 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39020 (p : Pattern) (guard : d316577 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316576 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39019 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39021 (p : Pattern) (guard : d316578 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316577 p = 1 := by simpa only [d316578, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39020 p hg
    simpa only [d316578, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316578, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d316578, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39022 (p : Pattern) (guard : d316775 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39021 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39008 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39023 (p : Pattern) (guard : d316776 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316775 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39022 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39024 (p : Pattern) (guard : d316777 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316776 p = 1 := by simpa only [d316777, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39023 p hg
    simpa only [d316777, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316777, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d316777, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39025 (p : Pattern) (guard : d317703 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39011 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39024 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39026 (p : Pattern) (guard : d317704 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317703 p = 1 := by simpa only [d317704, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39025 p hg
    simpa only [d317704, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317704, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317704, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39027 (p : Pattern) (guard : d317705 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317704 p = 1 := by simpa only [d317705, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39026 p hg
    simpa only [d317705, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317705, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317705, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39028 (p : Pattern) (guard : d317706 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317706, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317706, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317705 p = 1 := by simpa only [d317706, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39027 p hg
    simpa only [d317706, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39029 (p : Pattern) (guard : d317707 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317706 p = 1 := by simpa only [d317707, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39028 p hg
    simpa only [d317707, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317707, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317707, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39030 (p : Pattern) (guard : d317708 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317702 p = 1 := by simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39016 p hg
    simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317707 p = 1 := by simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39029 p hg
    simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39031 (p : Pattern) (guard : d316588 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316578 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39021 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39032 (p : Pattern) (guard : d316589 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316588 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39031 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39033 (p : Pattern) (guard : d316590 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316589 p = 1 := by simpa only [d316590, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39032 p hg
    simpa only [d316590, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316590, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d316590, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39034 (p : Pattern) (guard : d316784 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39033 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39024 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39035 (p : Pattern) (guard : d316785 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316784 p = 1 := by simpa only [d316785, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39034 p hg
    simpa only [d316785, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316785, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d316785, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39036 (p : Pattern) (guard : d316786 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316785 p = 1 := by simpa only [d316786, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39035 p hg
    simpa only [d316786, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316786, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316786, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39037 (p : Pattern) (guard : d316787 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316787, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d316787, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316786 p = 1 := by simpa only [d316787, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39036 p hg
    simpa only [d316787, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39038 (p : Pattern) (guard : d316788 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316787 p = 1 := by simpa only [d316788, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39037 p hg
    simpa only [d316788, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316788, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d316788, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39039 (p : Pattern) (guard : d317709 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39002 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39008 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39040 (p : Pattern) (guard : d258109 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39008 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39041 (p : Pattern) (guard : d317710 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317709 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39039 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39040 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39042 (p : Pattern) (guard : d317711 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317710 p = 1 := by simpa only [d317711, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39041 p hg
    simpa only [d317711, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317711, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d317711, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39043 (p : Pattern) (guard : d317712 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317711 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39042 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39044 (p : Pattern) (guard : d317713 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317712 p = 1 := by simpa only [d317713, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39043 p hg
    simpa only [d317713, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317713, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317713, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39045 (p : Pattern) (guard : d317714 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317713 p = 1 := by simpa only [d317714, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39044 p hg
    simpa only [d317714, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317714, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317714, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39046 (p : Pattern) (guard : d317715 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317715, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317715, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317714 p = 1 := by simpa only [d317715, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39045 p hg
    simpa only [d317715, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39047 (p : Pattern) (guard : d317716 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317715 p = 1 := by simpa only [d317716, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39046 p hg
    simpa only [d317716, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317716, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317716, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39048 (p : Pattern) (guard : d317717 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316788 p = 1 := by simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39038 p hg
    simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317716 p = 1 := by simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39047 p hg
    simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39049 (p : Pattern) (guard : d317718 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317708 p = 1 := by simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39030 p hg
    simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317717 p = 1 := by simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39048 p hg
    simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39050 (p : Pattern) (guard : d317719 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39002 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39051 (p : Pattern) (guard : d317720 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317719 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39050 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39040 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39052 (p : Pattern) (guard : d317721 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317720 p = 1 := by simpa only [d317721, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39051 p hg
    simpa only [d317721, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317721, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d317721, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39053 (p : Pattern) (guard : d317722 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39011 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317721 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39052 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39054 (p : Pattern) (guard : d317723 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317722 p = 1 := by simpa only [d317723, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39053 p hg
    simpa only [d317723, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317723, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317723, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39055 (p : Pattern) (guard : d317724 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317723 p = 1 := by simpa only [d317724, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39054 p hg
    simpa only [d317724, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317724, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317724, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39056 (p : Pattern) (guard : d317725 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317725, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317725, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317724 p = 1 := by simpa only [d317725, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39055 p hg
    simpa only [d317725, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39057 (p : Pattern) (guard : d317726 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317725 p = 1 := by simpa only [d317726, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39056 p hg
    simpa only [d317726, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317726, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317726, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39058 (p : Pattern) (guard : d317727 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317721 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39052 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39059 (p : Pattern) (guard : d317728 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317727 p = 1 := by simpa only [d317728, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39058 p hg
    simpa only [d317728, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317728, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317728, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39060 (p : Pattern) (guard : d317729 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317728 p = 1 := by simpa only [d317729, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39059 p hg
    simpa only [d317729, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317729, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317729, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39061 (p : Pattern) (guard : d317730 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317730, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317730, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317729 p = 1 := by simpa only [d317730, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39060 p hg
    simpa only [d317730, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39062 (p : Pattern) (guard : d317731 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317730 p = 1 := by simpa only [d317731, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39061 p hg
    simpa only [d317731, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317731, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317731, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39063 (p : Pattern) (guard : d317732 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317726 p = 1 := by simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39057 p hg
    simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317731 p = 1 := by simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39062 p hg
    simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39064 (p : Pattern) (guard : d317733 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317716 p = 1 := by simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39047 p hg
    simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39065 (p : Pattern) (guard : d317734 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317732 p = 1 := by simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39063 p hg
    simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317733 p = 1 := by simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39064 p hg
    simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39066 (p : Pattern) (guard : d317735 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317718 p = 1 := by simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39049 p hg
    simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317734 p = 1 := by simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39065 p hg
    simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39067 (p : Pattern) (guard : d317736 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317736, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d317736, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317735 p = 1 := by simpa only [d317736, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39066 p hg
    simpa only [d317736, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39068 (p : Pattern) (guard : d317737 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317737, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d317737, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317736 p = 1 := by simpa only [d317737, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39067 p hg
    simpa only [d317737, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39069 (p : Pattern) (guard : d317738 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317731 p = 1 := by simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39062 p hg
    simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39070 (p : Pattern) (guard : d317739 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317738 p = 1 := by simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39069 p hg
    simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39071 (p : Pattern) (guard : d317740 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317734 p = 1 := by simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39065 p hg
    simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317739 p = 1 := by simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39070 p hg
    simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39072 (p : Pattern) (guard : d317741 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317741, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d317741, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317740 p = 1 := by simpa only [d317741, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39071 p hg
    simpa only [d317741, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39073 (p : Pattern) (guard : d317742 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317742, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d317742, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317741 p = 1 := by simpa only [d317742, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39072 p hg
    simpa only [d317742, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39074 (p : Pattern) (guard : d317743 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317737 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39068 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317742 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39073 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39075 (p : Pattern) (guard : d317744 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317742 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39073 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39076 (p : Pattern) (guard : d317745 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317743 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39074 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317744 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39075 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39077 (p : Pattern) (guard : d317746 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317745 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39076 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39078 (p : Pattern) (guard : d317747 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317746 p = 1 := by simpa only [d317747, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39077 p hg
    simpa only [d317747, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317747, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d317747, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39079 (p : Pattern) (guard : d317748 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317748, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d317748, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317747 p = 1 := by simpa only [d317748, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39078 p hg
    simpa only [d317748, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39080 (p : Pattern) (guard : d317749 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317744 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39075 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39081 (p : Pattern) (guard : d317750 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317749 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39080 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39082 (p : Pattern) (guard : d317751 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317750 p = 1 := by simpa only [d317751, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39081 p hg
    simpa only [d317751, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317751, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d317751, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39083 (p : Pattern) (guard : d317752 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317752, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d317752, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317751 p = 1 := by simpa only [d317752, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39082 p hg
    simpa only [d317752, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39084 (p : Pattern) (guard : d317753 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39079 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317752 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39083 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39085 (p : Pattern) (guard : d317754 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317753 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39084 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39086 (p : Pattern) (guard : d317755 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317754 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39085 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39087 (p : Pattern) (guard : d317769 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317755 p = 1 := by simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39086 p hg
    simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39088 (p : Pattern) (guard : d317757 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317752 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39083 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39089 (p : Pattern) (guard : d317758 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317757 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39088 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39090 (p : Pattern) (guard : d317759 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317758 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39089 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39091 (p : Pattern) (guard : d317770 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317759 p = 1 := by simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39090 p hg
    simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39092 (p : Pattern) (guard : d317771 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317769 p = 1 := by simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39087 p hg
    simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317770 p = 1 := by simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39091 p hg
    simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39093 (p : Pattern) (guard : d317772 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317771 p = 1 := by simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39092 p hg
    simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39094 (p : Pattern) (guard : d317773 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317772 p = 1 := by simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39093 p hg
    simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39095 (p : Pattern) (guard : d317774 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317773 p = 1 := by simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39094 p hg
    simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39096 (p : Pattern) (guard : d317775 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317774 p = 1 := by simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39095 p hg
    simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39097 (p : Pattern) (guard : d318447 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318447, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318447, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317775 p = 1 := by simpa only [d318447, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39096 p hg
    simpa only [d318447, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39098 (p : Pattern) (guard : d318448 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318447 p = 1 := by simpa only [d318448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39097 p hg
    simpa only [d318448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39099 (p : Pattern) (guard : d318449 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318448 p = 1 := by simpa only [d318449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39098 p hg
    simpa only [d318449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39100 (p : Pattern) (guard : d318450 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318449 p = 1 := by simpa only [d318450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39099 p hg
    simpa only [d318450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39101 (p : Pattern) (guard : d318451 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318450 p = 1 := by simpa only [d318451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39100 p hg
    simpa only [d318451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39102 (p : Pattern) (guard : d318452 p = 1) : d50390 p ≤ (2 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318446 p = 1 := by simpa only [d318452, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38994 p hg
    simpa only [d318452, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318451 p = 1 := by simpa only [d318452, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39101 p hg
    simpa only [d318452, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39103 (p : Pattern) (guard : d34355 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34354 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38685 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39104 (p : Pattern) (guard : d34356 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34355 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39103 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39105 (p : Pattern) (guard : d34357 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d34356 p = 1 := by simpa only [d34357, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39104 p hg
    simpa only [d34357, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34357, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d34357, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39106 (p : Pattern) (guard : d40834 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare39107 (p : Pattern) (guard : d317691 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40834 p = 1 := by simpa only [d317691, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39106 p hg
    simpa only [d317691, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317691, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d317691, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39108 (p : Pattern) (guard : d317692 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317691 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39107 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39109 (p : Pattern) (guard : d317693 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317692 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39108 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39110 (p : Pattern) (guard : d317694 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317693 p = 1 := by simpa only [d317694, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39109 p hg
    simpa only [d317694, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317694, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d317694, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39111 (p : Pattern) (guard : d317695 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317694 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39110 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39112 (p : Pattern) (guard : d1531 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare39113 (p : Pattern) (guard : d1547 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39112 p hg
    simpa only [d1547, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d1547, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39114 (p : Pattern) (guard : d39244 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39113 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39115 (p : Pattern) (guard : d258107 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39114 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39116 (p : Pattern) (guard : d258108 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39115 p hg
    simpa only [d258108, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d258108, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39117 (p : Pattern) (guard : d316767 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38685 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39116 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39118 (p : Pattern) (guard : d317696 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317695 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39111 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316767 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39117 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39119 (p : Pattern) (guard : d317697 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317696 p = 1 := by simpa only [d317697, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39118 p hg
    simpa only [d317697, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317697, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d317697, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39120 (p : Pattern) (guard : d317698 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39105 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317697 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39119 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39121 (p : Pattern) (guard : d317873 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317698 p = 1 := by simpa only [d317873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39120 p hg
    simpa only [d317873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39122 (p : Pattern) (guard : d317699 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317698 p = 1 := by simpa only [d317699, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38872 p hg
    simpa only [d317699, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317699, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317699, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39123 (p : Pattern) (guard : d317874 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317873 p = 1 := by simpa only [d317874, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39121 p hg
    simpa only [d317874, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317699 p = 1 := by simpa only [d317874, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39122 p hg
    simpa only [d317874, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39124 (p : Pattern) (guard : d34355 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34354 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38706 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39125 (p : Pattern) (guard : d34356 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34355 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39124 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39126 (p : Pattern) (guard : d34357 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d34356 p = 1 := by simpa only [d34357, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39125 p hg
    simpa only [d34357, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34357, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d34357, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39127 (p : Pattern) (guard : d40834 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare39128 (p : Pattern) (guard : d317691 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40834 p = 1 := by simpa only [d317691, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39127 p hg
    simpa only [d317691, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317691, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d317691, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39129 (p : Pattern) (guard : d317692 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317691 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39128 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39130 (p : Pattern) (guard : d317693 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317692 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39129 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39131 (p : Pattern) (guard : d317694 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317693 p = 1 := by simpa only [d317694, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39130 p hg
    simpa only [d317694, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317694, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d317694, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39132 (p : Pattern) (guard : d317695 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317694 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39131 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39133 (p : Pattern) (guard : d1531 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare39134 (p : Pattern) (guard : d1547 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39133 p hg
    simpa only [d1547, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d1547, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39135 (p : Pattern) (guard : d39244 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39134 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39136 (p : Pattern) (guard : d258107 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39135 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39137 (p : Pattern) (guard : d258108 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39136 p hg
    simpa only [d258108, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d258108, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39138 (p : Pattern) (guard : d316767 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38706 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39137 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39139 (p : Pattern) (guard : d317696 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317695 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39132 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316767 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39138 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39140 (p : Pattern) (guard : d317697 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317696 p = 1 := by simpa only [d317697, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39139 p hg
    simpa only [d317697, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317697, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d317697, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39141 (p : Pattern) (guard : d317698 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39126 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317697 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39142 (p : Pattern) (guard : d317699 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317698 p = 1 := by simpa only [d317699, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39141 p hg
    simpa only [d317699, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317699, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317699, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39143 (p : Pattern) (guard : d317700 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317699 p = 1 := by simpa only [d317700, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39142 p hg
    simpa only [d317700, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317700, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317700, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39144 (p : Pattern) (guard : d317875 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317874 p = 1 := by simpa only [d317875, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39123 p hg
    simpa only [d317875, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317700 p = 1 := by simpa only [d317875, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39143 p hg
    simpa only [d317875, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39145 (p : Pattern) (guard : d317876 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317875 p = 1 := by simpa only [d317876, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39144 p hg
    simpa only [d317876, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317876, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317876, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39146 (p : Pattern) (guard : d34366 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare39147 (p : Pattern) (guard : d34367 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d34366 p = 1 := by simpa only [d34367, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39146 p hg
    simpa only [d34367, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34367, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d34367, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39148 (p : Pattern) (guard : d316576 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34367 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39147 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39149 (p : Pattern) (guard : d316577 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316576 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39148 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39150 (p : Pattern) (guard : d316578 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316577 p = 1 := by simpa only [d316578, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39149 p hg
    simpa only [d316578, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316578, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d316578, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39151 (p : Pattern) (guard : d316775 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39150 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39116 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39152 (p : Pattern) (guard : d316776 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316775 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39151 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39153 (p : Pattern) (guard : d316777 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316776 p = 1 := by simpa only [d316777, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39152 p hg
    simpa only [d316777, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316777, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d316777, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39154 (p : Pattern) (guard : d317703 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39119 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39153 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39155 (p : Pattern) (guard : d317877 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317703 p = 1 := by simpa only [d317877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39154 p hg
    simpa only [d317877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39156 (p : Pattern) (guard : d317704 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317703 p = 1 := by simpa only [d317704, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38885 p hg
    simpa only [d317704, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317704, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317704, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39157 (p : Pattern) (guard : d317878 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317877 p = 1 := by simpa only [d317878, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39155 p hg
    simpa only [d317878, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317704 p = 1 := by simpa only [d317878, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39156 p hg
    simpa only [d317878, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39158 (p : Pattern) (guard : d34366 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare39159 (p : Pattern) (guard : d34367 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d34366 p = 1 := by simpa only [d34367, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39158 p hg
    simpa only [d34367, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34367, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d34367, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39160 (p : Pattern) (guard : d316576 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34367 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39159 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39161 (p : Pattern) (guard : d316577 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316576 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39160 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39162 (p : Pattern) (guard : d316578 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316577 p = 1 := by simpa only [d316578, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39161 p hg
    simpa only [d316578, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316578, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d316578, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39163 (p : Pattern) (guard : d316775 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39162 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39137 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39164 (p : Pattern) (guard : d316776 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316775 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39163 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39165 (p : Pattern) (guard : d316777 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316776 p = 1 := by simpa only [d316777, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39164 p hg
    simpa only [d316777, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316777, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d316777, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39166 (p : Pattern) (guard : d317703 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39165 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39167 (p : Pattern) (guard : d317704 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317703 p = 1 := by simpa only [d317704, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39166 p hg
    simpa only [d317704, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317704, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317704, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39168 (p : Pattern) (guard : d317705 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317704 p = 1 := by simpa only [d317705, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39167 p hg
    simpa only [d317705, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317705, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317705, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39169 (p : Pattern) (guard : d317879 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317878 p = 1 := by simpa only [d317879, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39157 p hg
    simpa only [d317879, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317705 p = 1 := by simpa only [d317879, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39168 p hg
    simpa only [d317879, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39170 (p : Pattern) (guard : d317880 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317879 p = 1 := by simpa only [d317880, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39169 p hg
    simpa only [d317880, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317880, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317880, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39171 (p : Pattern) (guard : d317881 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317876 p = 1 := by simpa only [d317881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39145 p hg
    simpa only [d317881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317880 p = 1 := by simpa only [d317881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39170 p hg
    simpa only [d317881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39172 (p : Pattern) (guard : d316588 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316578 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39150 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39173 (p : Pattern) (guard : d316589 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316588 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39172 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39174 (p : Pattern) (guard : d316590 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316589 p = 1 := by simpa only [d316590, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39173 p hg
    simpa only [d316590, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316590, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d316590, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39175 (p : Pattern) (guard : d316784 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39174 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39153 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39176 (p : Pattern) (guard : d316965 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d316965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316784 p = 1 := by simpa only [d316965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39175 p hg
    simpa only [d316965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39177 (p : Pattern) (guard : d316785 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316784 p = 1 := by simpa only [d316785, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38894 p hg
    simpa only [d316785, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316785, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d316785, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39178 (p : Pattern) (guard : d316966 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316965 p = 1 := by simpa only [d316966, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39176 p hg
    simpa only [d316966, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316785 p = 1 := by simpa only [d316966, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39177 p hg
    simpa only [d316966, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39179 (p : Pattern) (guard : d316588 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316578 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39162 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39180 (p : Pattern) (guard : d316589 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316588 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39179 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39181 (p : Pattern) (guard : d316590 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316589 p = 1 := by simpa only [d316590, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39180 p hg
    simpa only [d316590, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316590, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d316590, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39182 (p : Pattern) (guard : d316784 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39181 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39165 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39183 (p : Pattern) (guard : d316785 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316784 p = 1 := by simpa only [d316785, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39182 p hg
    simpa only [d316785, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316785, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316785, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39184 (p : Pattern) (guard : d316786 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316785 p = 1 := by simpa only [d316786, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39183 p hg
    simpa only [d316786, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316786, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316786, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39185 (p : Pattern) (guard : d316967 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316966 p = 1 := by simpa only [d316967, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39178 p hg
    simpa only [d316967, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316786 p = 1 := by simpa only [d316967, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39184 p hg
    simpa only [d316967, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39186 (p : Pattern) (guard : d316968 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316967 p = 1 := by simpa only [d316968, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39185 p hg
    simpa only [d316968, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316968, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d316968, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39187 (p : Pattern) (guard : d317709 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39110 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39116 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39188 (p : Pattern) (guard : d258109 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39116 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39189 (p : Pattern) (guard : d317710 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317709 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39187 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39188 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39190 (p : Pattern) (guard : d317711 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317710 p = 1 := by simpa only [d317711, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39189 p hg
    simpa only [d317711, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317711, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d317711, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39191 (p : Pattern) (guard : d317712 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317711 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39190 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39192 (p : Pattern) (guard : d317882 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317712 p = 1 := by simpa only [d317882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39191 p hg
    simpa only [d317882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39193 (p : Pattern) (guard : d317713 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317712 p = 1 := by simpa only [d317713, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38903 p hg
    simpa only [d317713, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317713, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317713, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39194 (p : Pattern) (guard : d317883 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317882 p = 1 := by simpa only [d317883, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39192 p hg
    simpa only [d317883, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317713 p = 1 := by simpa only [d317883, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39193 p hg
    simpa only [d317883, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39195 (p : Pattern) (guard : d317709 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39131 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39137 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39196 (p : Pattern) (guard : d258109 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39137 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39197 (p : Pattern) (guard : d317710 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317709 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39195 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39196 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39198 (p : Pattern) (guard : d317711 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317710 p = 1 := by simpa only [d317711, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39197 p hg
    simpa only [d317711, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317711, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d317711, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39199 (p : Pattern) (guard : d317712 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317711 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39198 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39200 (p : Pattern) (guard : d317713 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317712 p = 1 := by simpa only [d317713, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39199 p hg
    simpa only [d317713, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317713, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317713, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39201 (p : Pattern) (guard : d317714 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317713 p = 1 := by simpa only [d317714, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39200 p hg
    simpa only [d317714, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317714, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317714, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39202 (p : Pattern) (guard : d317884 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317883 p = 1 := by simpa only [d317884, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39194 p hg
    simpa only [d317884, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317714 p = 1 := by simpa only [d317884, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39201 p hg
    simpa only [d317884, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39203 (p : Pattern) (guard : d317885 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317884 p = 1 := by simpa only [d317885, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39202 p hg
    simpa only [d317885, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317885, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317885, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39204 (p : Pattern) (guard : d317886 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316968 p = 1 := by simpa only [d317886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39186 p hg
    simpa only [d317886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317885 p = 1 := by simpa only [d317886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39203 p hg
    simpa only [d317886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39205 (p : Pattern) (guard : d317887 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317881 p = 1 := by simpa only [d317887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39171 p hg
    simpa only [d317887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317886 p = 1 := by simpa only [d317887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39204 p hg
    simpa only [d317887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39206 (p : Pattern) (guard : d317719 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39110 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39207 (p : Pattern) (guard : d317720 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317719 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39206 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39188 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39208 (p : Pattern) (guard : d317721 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317720 p = 1 := by simpa only [d317721, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39207 p hg
    simpa only [d317721, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317721, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d317721, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39209 (p : Pattern) (guard : d317722 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39119 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317721 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39208 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39210 (p : Pattern) (guard : d317897 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317722 p = 1 := by simpa only [d317897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39209 p hg
    simpa only [d317897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39211 (p : Pattern) (guard : d317723 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317722 p = 1 := by simpa only [d317723, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38913 p hg
    simpa only [d317723, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317723, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317723, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39212 (p : Pattern) (guard : d317898 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317897 p = 1 := by simpa only [d317898, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39210 p hg
    simpa only [d317898, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317723 p = 1 := by simpa only [d317898, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39211 p hg
    simpa only [d317898, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39213 (p : Pattern) (guard : d317719 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39131 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39214 (p : Pattern) (guard : d317720 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317719 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39213 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39196 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39215 (p : Pattern) (guard : d317721 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317720 p = 1 := by simpa only [d317721, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39214 p hg
    simpa only [d317721, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317721, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d317721, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39216 (p : Pattern) (guard : d317722 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317721 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39215 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39217 (p : Pattern) (guard : d317723 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317722 p = 1 := by simpa only [d317723, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39216 p hg
    simpa only [d317723, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317723, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317723, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39218 (p : Pattern) (guard : d317724 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317723 p = 1 := by simpa only [d317724, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39217 p hg
    simpa only [d317724, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317724, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317724, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39219 (p : Pattern) (guard : d317899 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317898 p = 1 := by simpa only [d317899, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39212 p hg
    simpa only [d317899, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317724 p = 1 := by simpa only [d317899, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39218 p hg
    simpa only [d317899, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39220 (p : Pattern) (guard : d317900 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317899 p = 1 := by simpa only [d317900, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39219 p hg
    simpa only [d317900, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317900, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317900, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39221 (p : Pattern) (guard : d317727 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317721 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39208 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39222 (p : Pattern) (guard : d317901 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317727 p = 1 := by simpa only [d317901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39221 p hg
    simpa only [d317901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39223 (p : Pattern) (guard : d317728 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317727 p = 1 := by simpa only [d317728, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38918 p hg
    simpa only [d317728, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317728, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317728, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39224 (p : Pattern) (guard : d317902 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317901 p = 1 := by simpa only [d317902, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39222 p hg
    simpa only [d317902, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317728 p = 1 := by simpa only [d317902, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39223 p hg
    simpa only [d317902, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39225 (p : Pattern) (guard : d317727 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317721 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39215 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39226 (p : Pattern) (guard : d317728 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317727 p = 1 := by simpa only [d317728, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39225 p hg
    simpa only [d317728, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317728, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317728, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39227 (p : Pattern) (guard : d317729 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317728 p = 1 := by simpa only [d317729, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39226 p hg
    simpa only [d317729, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317729, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317729, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39228 (p : Pattern) (guard : d317903 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317902 p = 1 := by simpa only [d317903, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39224 p hg
    simpa only [d317903, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317729 p = 1 := by simpa only [d317903, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39227 p hg
    simpa only [d317903, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39229 (p : Pattern) (guard : d317904 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317903 p = 1 := by simpa only [d317904, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39228 p hg
    simpa only [d317904, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317904, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317904, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39230 (p : Pattern) (guard : d317905 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317900 p = 1 := by simpa only [d317905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39220 p hg
    simpa only [d317905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317904 p = 1 := by simpa only [d317905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39229 p hg
    simpa only [d317905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39231 (p : Pattern) (guard : d317891 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317885 p = 1 := by simpa only [d317891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39203 p hg
    simpa only [d317891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39232 (p : Pattern) (guard : d317906 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317905 p = 1 := by simpa only [d317906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39230 p hg
    simpa only [d317906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317891 p = 1 := by simpa only [d317906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39231 p hg
    simpa only [d317906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39233 (p : Pattern) (guard : d317907 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317887 p = 1 := by simpa only [d317907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39205 p hg
    simpa only [d317907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317906 p = 1 := by simpa only [d317907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39232 p hg
    simpa only [d317907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39234 (p : Pattern) (guard : d317908 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317908, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d317908, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317907 p = 1 := by simpa only [d317908, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39233 p hg
    simpa only [d317908, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39235 (p : Pattern) (guard : d317909 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317909, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d317909, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317908 p = 1 := by simpa only [d317909, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d317909, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39236 (p : Pattern) (guard : d317910 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317904 p = 1 := by simpa only [d317910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39229 p hg
    simpa only [d317910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39237 (p : Pattern) (guard : d317911 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317910 p = 1 := by simpa only [d317911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39236 p hg
    simpa only [d317911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39238 (p : Pattern) (guard : d317912 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317906 p = 1 := by simpa only [d317912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39232 p hg
    simpa only [d317912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317911 p = 1 := by simpa only [d317912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39237 p hg
    simpa only [d317912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39239 (p : Pattern) (guard : d317913 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317913, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d317913, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317912 p = 1 := by simpa only [d317913, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39238 p hg
    simpa only [d317913, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39240 (p : Pattern) (guard : d317914 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317914, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d317914, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317913 p = 1 := by simpa only [d317914, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39239 p hg
    simpa only [d317914, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39241 (p : Pattern) (guard : d317915 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317909 p = 1 := by simpa only [d317915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39235 p hg
    simpa only [d317915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317914 p = 1 := by simpa only [d317915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39240 p hg
    simpa only [d317915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39242 (p : Pattern) (guard : d317920 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317914 p = 1 := by simpa only [d317920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39240 p hg
    simpa only [d317920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d317920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39243 (p : Pattern) (guard : d317921 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317915 p = 1 := by simpa only [d317921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39241 p hg
    simpa only [d317921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317920 p = 1 := by simpa only [d317921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39242 p hg
    simpa only [d317921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39244 (p : Pattern) (guard : d317922 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317921 p = 1 := by simpa only [d317922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39243 p hg
    simpa only [d317922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d317922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39245 (p : Pattern) (guard : d317923 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317922 p = 1 := by simpa only [d317923, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39244 p hg
    simpa only [d317923, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317923, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d317923, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39246 (p : Pattern) (guard : d317924 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317924, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317924, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317923 p = 1 := by simpa only [d317924, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39245 p hg
    simpa only [d317924, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39247 (p : Pattern) (guard : d317929 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317920 p = 1 := by simpa only [d317929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39242 p hg
    simpa only [d317929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d317929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39248 (p : Pattern) (guard : d317930 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317929 p = 1 := by simpa only [d317930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39247 p hg
    simpa only [d317930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d317930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39249 (p : Pattern) (guard : d317931 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317930 p = 1 := by simpa only [d317931, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39248 p hg
    simpa only [d317931, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317931, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d317931, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
