import NetHack.Soko22Hazard87.Compare147
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37000 (p : Pattern) (guard : d317713 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317712 p = 1 := by simpa only [d317713, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36999 p hg
    simpa only [d317713, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317713, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317713, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37001 (p : Pattern) (guard : d317714 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317713 p = 1 := by simpa only [d317714, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37000 p hg
    simpa only [d317714, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317714, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317714, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37002 (p : Pattern) (guard : d317715 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317715, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317715, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317714 p = 1 := by simpa only [d317715, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37001 p hg
    simpa only [d317715, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37003 (p : Pattern) (guard : d317716 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317715 p = 1 := by simpa only [d317716, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37002 p hg
    simpa only [d317716, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317716, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317716, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37004 (p : Pattern) (guard : d317717 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316788 p = 1 := by simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36972 p hg
    simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317716 p = 1 := by simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37005 (p : Pattern) (guard : d317718 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317708 p = 1 := by simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36994 p hg
    simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317717 p = 1 := by simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37004 p hg
    simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37006 (p : Pattern) (guard : d317797 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316875 p = 1 := by simpa only [d317797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36974 p hg
    simpa only [d317797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317718 p = 1 := by simpa only [d317797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37005 p hg
    simpa only [d317797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37007 (p : Pattern) (guard : d317798 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317798, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317798, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317797 p = 1 := by simpa only [d317798, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37006 p hg
    simpa only [d317798, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37008 (p : Pattern) (guard : d317799 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317799, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317799, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317798 p = 1 := by simpa only [d317799, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37007 p hg
    simpa only [d317799, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37009 (p : Pattern) (guard : d317733 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317716 p = 1 := by simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37010 (p : Pattern) (guard : d317800 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317717 p = 1 := by simpa only [d317800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37004 p hg
    simpa only [d317800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317733 p = 1 := by simpa only [d317800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37009 p hg
    simpa only [d317800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37011 (p : Pattern) (guard : d317801 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317718 p = 1 := by simpa only [d317801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37005 p hg
    simpa only [d317801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317800 p = 1 := by simpa only [d317801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37010 p hg
    simpa only [d317801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37012 (p : Pattern) (guard : d317802 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317802, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317802, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317801 p = 1 := by simpa only [d317802, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37011 p hg
    simpa only [d317802, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37013 (p : Pattern) (guard : d317803 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317803, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317803, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317802 p = 1 := by simpa only [d317803, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37012 p hg
    simpa only [d317803, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37014 (p : Pattern) (guard : d317804 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317799 p = 1 := by simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37008 p hg
    simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317803 p = 1 := by simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37013 p hg
    simpa only [d317804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37015 (p : Pattern) (guard : d317719 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36979 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37016 (p : Pattern) (guard : d317720 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317719 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37015 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36996 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37017 (p : Pattern) (guard : d317721 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317720 p = 1 := by simpa only [d317721, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37016 p hg
    simpa only [d317721, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317721, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d317721, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37018 (p : Pattern) (guard : d317722 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317721 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37017 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37019 (p : Pattern) (guard : d317723 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317722 p = 1 := by simpa only [d317723, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37018 p hg
    simpa only [d317723, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317723, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317723, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37020 (p : Pattern) (guard : d317724 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317723 p = 1 := by simpa only [d317724, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37019 p hg
    simpa only [d317724, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317724, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317724, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37021 (p : Pattern) (guard : d317725 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317725, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317725, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317724 p = 1 := by simpa only [d317725, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37020 p hg
    simpa only [d317725, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37022 (p : Pattern) (guard : d317726 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317725 p = 1 := by simpa only [d317726, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37021 p hg
    simpa only [d317726, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317726, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317726, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37023 (p : Pattern) (guard : d317727 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317721 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37017 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37024 (p : Pattern) (guard : d317728 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317727 p = 1 := by simpa only [d317728, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37023 p hg
    simpa only [d317728, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317728, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317728, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37025 (p : Pattern) (guard : d317729 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317728 p = 1 := by simpa only [d317729, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37024 p hg
    simpa only [d317729, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317729, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317729, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37026 (p : Pattern) (guard : d317730 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317730, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317730, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317729 p = 1 := by simpa only [d317730, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37025 p hg
    simpa only [d317730, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37027 (p : Pattern) (guard : d317731 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317730 p = 1 := by simpa only [d317731, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37026 p hg
    simpa only [d317731, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317731, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317731, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37028 (p : Pattern) (guard : d317732 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317726 p = 1 := by simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37022 p hg
    simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317731 p = 1 := by simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37027 p hg
    simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37029 (p : Pattern) (guard : d317734 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317732 p = 1 := by simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37028 p hg
    simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317733 p = 1 := by simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37009 p hg
    simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37030 (p : Pattern) (guard : d317735 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317718 p = 1 := by simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37005 p hg
    simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317734 p = 1 := by simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37029 p hg
    simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37031 (p : Pattern) (guard : d317736 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317736, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317736, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317735 p = 1 := by simpa only [d317736, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37030 p hg
    simpa only [d317736, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37032 (p : Pattern) (guard : d317737 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317737, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317737, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317736 p = 1 := by simpa only [d317737, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37031 p hg
    simpa only [d317737, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37033 (p : Pattern) (guard : d317738 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317731 p = 1 := by simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37027 p hg
    simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37034 (p : Pattern) (guard : d317739 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317738 p = 1 := by simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37033 p hg
    simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37035 (p : Pattern) (guard : d317740 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317734 p = 1 := by simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37029 p hg
    simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317739 p = 1 := by simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37034 p hg
    simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37036 (p : Pattern) (guard : d317741 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317741, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317741, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317740 p = 1 := by simpa only [d317741, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37035 p hg
    simpa only [d317741, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37037 (p : Pattern) (guard : d317742 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317742, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317742, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317741 p = 1 := by simpa only [d317742, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37036 p hg
    simpa only [d317742, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37038 (p : Pattern) (guard : d317743 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317737 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37032 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317742 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37037 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37039 (p : Pattern) (guard : d317805 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317804 p = 1 := by simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37014 p hg
    simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317743 p = 1 := by simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37038 p hg
    simpa only [d317805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37040 (p : Pattern) (guard : d317806 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317805 p = 1 := by simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37039 p hg
    simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37041 (p : Pattern) (guard : d317807 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317806 p = 1 := by simpa only [d317807, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37040 p hg
    simpa only [d317807, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317807, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d317807, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37042 (p : Pattern) (guard : d317808 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317808, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d317808, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317807 p = 1 := by simpa only [d317808, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37041 p hg
    simpa only [d317808, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37043 (p : Pattern) (guard : d317744 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317742 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37037 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37044 (p : Pattern) (guard : d317745 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317743 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37038 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317744 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37043 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37045 (p : Pattern) (guard : d317746 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317745 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37044 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37046 (p : Pattern) (guard : d317747 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317746 p = 1 := by simpa only [d317747, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37045 p hg
    simpa only [d317747, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317747, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d317747, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37047 (p : Pattern) (guard : d317748 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317748, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d317748, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317747 p = 1 := by simpa only [d317748, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37046 p hg
    simpa only [d317748, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37048 (p : Pattern) (guard : d317809 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317808 p = 1 := by simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37042 p hg
    simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317748 p = 1 := by simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37047 p hg
    simpa only [d317809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37049 (p : Pattern) (guard : d317810 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317809 p = 1 := by simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37048 p hg
    simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37050 (p : Pattern) (guard : d317811 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317810 p = 1 := by simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37049 p hg
    simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37051 (p : Pattern) (guard : d317836 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317811 p = 1 := by simpa only [d317836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37050 p hg
    simpa only [d317836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37052 (p : Pattern) (guard : d317749 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317744 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37043 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37053 (p : Pattern) (guard : d317750 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317749 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37052 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37054 (p : Pattern) (guard : d317751 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317750 p = 1 := by simpa only [d317751, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37053 p hg
    simpa only [d317751, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317751, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d317751, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37055 (p : Pattern) (guard : d317752 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317752, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d317752, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317751 p = 1 := by simpa only [d317752, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37054 p hg
    simpa only [d317752, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37056 (p : Pattern) (guard : d317753 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37047 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317752 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37055 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37057 (p : Pattern) (guard : d317754 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317753 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37056 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37058 (p : Pattern) (guard : d317755 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317754 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37057 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37059 (p : Pattern) (guard : d317769 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317755 p = 1 := by simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37058 p hg
    simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37060 (p : Pattern) (guard : d317837 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317836 p = 1 := by simpa only [d317837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37051 p hg
    simpa only [d317837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317769 p = 1 := by simpa only [d317837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37059 p hg
    simpa only [d317837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37061 (p : Pattern) (guard : d317838 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317837 p = 1 := by simpa only [d317838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37060 p hg
    simpa only [d317838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37062 (p : Pattern) (guard : d317815 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37047 p hg
    simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37063 (p : Pattern) (guard : d317816 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317815 p = 1 := by simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37062 p hg
    simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37064 (p : Pattern) (guard : d317817 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317816 p = 1 := by simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37063 p hg
    simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37065 (p : Pattern) (guard : d317839 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317817 p = 1 := by simpa only [d317839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37064 p hg
    simpa only [d317839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37066 (p : Pattern) (guard : d317840 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317839 p = 1 := by simpa only [d317840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37065 p hg
    simpa only [d317840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37067 (p : Pattern) (guard : d317841 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317840 p = 1 := by simpa only [d317841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37066 p hg
    simpa only [d317841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37068 (p : Pattern) (guard : d317842 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317838 p = 1 := by simpa only [d317842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37061 p hg
    simpa only [d317842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317841 p = 1 := by simpa only [d317842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37067 p hg
    simpa only [d317842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37069 (p : Pattern) (guard : d317863 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317842 p = 1 := by simpa only [d317863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37068 p hg
    simpa only [d317863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37070 (p : Pattern) (guard : d317864 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317863 p = 1 := by simpa only [d317864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37069 p hg
    simpa only [d317864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37071 (p : Pattern) (guard : d317865 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317865, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317865, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317864 p = 1 := by simpa only [d317865, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37070 p hg
    simpa only [d317865, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37072 (p : Pattern) (guard : d317866 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d317866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317865 p = 1 := by simpa only [d317866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37071 p hg
    simpa only [d317866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37073 (p : Pattern) (guard : d317757 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317752 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37055 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37074 (p : Pattern) (guard : d317758 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317757 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37075 (p : Pattern) (guard : d317759 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317758 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37074 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37076 (p : Pattern) (guard : d317770 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317759 p = 1 := by simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37075 p hg
    simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37077 (p : Pattern) (guard : d317853 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317770 p = 1 := by simpa only [d317853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37076 p hg
    simpa only [d317853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37078 (p : Pattern) (guard : d317854 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317853 p = 1 := by simpa only [d317854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37077 p hg
    simpa only [d317854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37079 (p : Pattern) (guard : d317855 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317854 p = 1 := by simpa only [d317855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37078 p hg
    simpa only [d317855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37080 (p : Pattern) (guard : d317856 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317855 p = 1 := by simpa only [d317856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37079 p hg
    simpa only [d317856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37081 (p : Pattern) (guard : d317857 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317856 p = 1 := by simpa only [d317857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37080 p hg
    simpa only [d317857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37082 (p : Pattern) (guard : d317867 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317867, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317867, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317857 p = 1 := by simpa only [d317867, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37081 p hg
    simpa only [d317867, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37083 (p : Pattern) (guard : d317868 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d317868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317867 p = 1 := by simpa only [d317868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37082 p hg
    simpa only [d317868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37084 (p : Pattern) (guard : d317869 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317866 p = 1 := by simpa only [d317869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37072 p hg
    simpa only [d317869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317868 p = 1 := by simpa only [d317869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37083 p hg
    simpa only [d317869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37085 (p : Pattern) (guard : d317870 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317869 p = 1 := by simpa only [d317870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37084 p hg
    simpa only [d317870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d317870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37086 (p : Pattern) (guard : d317871 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d317870 p = 1 := by simpa only [d317871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37085 p hg
    simpa only [d317871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d317871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37087 (p : Pattern) (guard : d317872 p = 1) : d50390 p ≤ (3 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d317862 p = 1 := by simpa only [d317872, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36943 p hg
    simpa only [d317872, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317871 p = 1 := by simpa only [d317872, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37086 p hg
    simpa only [d317872, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37088 (p : Pattern) (guard : d316858 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34357 p = 1 := by simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36458 p hg
    simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37089 (p : Pattern) (guard : d316952 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316858 p = 1 := by simpa only [d316952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37088 p hg
    simpa only [d316952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37090 (p : Pattern) (guard : d316859 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316858 p = 1 := by simpa only [d316859, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36816 p hg
    simpa only [d316859, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316859, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316859, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37091 (p : Pattern) (guard : d316953 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316952 p = 1 := by simpa only [d316953, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37089 p hg
    simpa only [d316953, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316859 p = 1 := by simpa only [d316953, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37090 p hg
    simpa only [d316953, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37092 (p : Pattern) (guard : d316858 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34357 p = 1 := by simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36465 p hg
    simpa only [d316858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37093 (p : Pattern) (guard : d316859 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316858 p = 1 := by simpa only [d316859, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37092 p hg
    simpa only [d316859, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316859, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316859, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37094 (p : Pattern) (guard : d316860 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316859 p = 1 := by simpa only [d316860, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37093 p hg
    simpa only [d316860, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316860, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316860, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37095 (p : Pattern) (guard : d316954 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316953 p = 1 := by simpa only [d316954, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37091 p hg
    simpa only [d316954, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316860 p = 1 := by simpa only [d316954, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37094 p hg
    simpa only [d316954, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37096 (p : Pattern) (guard : d316955 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316954 p = 1 := by simpa only [d316955, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37095 p hg
    simpa only [d316955, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316955, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316955, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37097 (p : Pattern) (guard : d316863 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36458 p hg
    simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316590 p = 1 := by simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37098 (p : Pattern) (guard : d316956 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316863 p = 1 := by simpa only [d316956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37097 p hg
    simpa only [d316956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37099 (p : Pattern) (guard : d316864 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316863 p = 1 := by simpa only [d316864, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36821 p hg
    simpa only [d316864, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316864, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316864, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37100 (p : Pattern) (guard : d316957 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316956 p = 1 := by simpa only [d316957, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37098 p hg
    simpa only [d316957, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316864 p = 1 := by simpa only [d316957, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37099 p hg
    simpa only [d316957, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37101 (p : Pattern) (guard : d316863 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36465 p hg
    simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316590 p = 1 := by simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36506 p hg
    simpa only [d316863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37102 (p : Pattern) (guard : d316864 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316863 p = 1 := by simpa only [d316864, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37101 p hg
    simpa only [d316864, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316864, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316864, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37103 (p : Pattern) (guard : d316865 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316864 p = 1 := by simpa only [d316865, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37102 p hg
    simpa only [d316865, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316865, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316865, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37104 (p : Pattern) (guard : d316958 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316957 p = 1 := by simpa only [d316958, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37100 p hg
    simpa only [d316958, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316865 p = 1 := by simpa only [d316958, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37103 p hg
    simpa only [d316958, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37105 (p : Pattern) (guard : d316959 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316958 p = 1 := by simpa only [d316959, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37104 p hg
    simpa only [d316959, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316959, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316959, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37106 (p : Pattern) (guard : d316960 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316955 p = 1 := by simpa only [d316960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37096 p hg
    simpa only [d316960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316959 p = 1 := by simpa only [d316960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37105 p hg
    simpa only [d316960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37107 (p : Pattern) (guard : d316869 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316590 p = 1 := by simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37108 (p : Pattern) (guard : d316961 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316869 p = 1 := by simpa only [d316961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37107 p hg
    simpa only [d316961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37109 (p : Pattern) (guard : d316870 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316869 p = 1 := by simpa only [d316870, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36827 p hg
    simpa only [d316870, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316870, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316870, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37110 (p : Pattern) (guard : d316962 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316961 p = 1 := by simpa only [d316962, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37108 p hg
    simpa only [d316962, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316870 p = 1 := by simpa only [d316962, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37109 p hg
    simpa only [d316962, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37111 (p : Pattern) (guard : d316869 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316590 p = 1 := by simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36506 p hg
    simpa only [d316869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37112 (p : Pattern) (guard : d316870 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316869 p = 1 := by simpa only [d316870, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37111 p hg
    simpa only [d316870, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316870, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316870, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37113 (p : Pattern) (guard : d316871 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316870 p = 1 := by simpa only [d316871, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37112 p hg
    simpa only [d316871, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316871, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316871, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37114 (p : Pattern) (guard : d316963 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316962 p = 1 := by simpa only [d316963, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37110 p hg
    simpa only [d316963, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316871 p = 1 := by simpa only [d316963, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37113 p hg
    simpa only [d316963, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37115 (p : Pattern) (guard : d316964 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316963 p = 1 := by simpa only [d316964, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37114 p hg
    simpa only [d316964, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316964, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316964, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37116 (p : Pattern) (guard : d1531 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare37117 (p : Pattern) (guard : d1547 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37116 p hg
    simpa only [d1547, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d1547, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37118 (p : Pattern) (guard : d39244 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37117 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37119 (p : Pattern) (guard : d258107 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37118 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37120 (p : Pattern) (guard : d258108 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37119 p hg
    simpa only [d258108, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d258108, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37121 (p : Pattern) (guard : d316775 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36475 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37120 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37122 (p : Pattern) (guard : d316776 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316775 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37121 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37123 (p : Pattern) (guard : d316777 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316776 p = 1 := by simpa only [d316777, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37122 p hg
    simpa only [d316777, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316777, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d316777, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37124 (p : Pattern) (guard : d316784 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37123 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37125 (p : Pattern) (guard : d316965 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316784 p = 1 := by simpa only [d316965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37124 p hg
    simpa only [d316965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37126 (p : Pattern) (guard : d316785 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316784 p = 1 := by simpa only [d316785, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36697 p hg
    simpa only [d316785, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316785, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316785, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37127 (p : Pattern) (guard : d316966 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316965 p = 1 := by simpa only [d316966, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37125 p hg
    simpa only [d316966, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316785 p = 1 := by simpa only [d316966, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37126 p hg
    simpa only [d316966, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37128 (p : Pattern) (guard : d1531 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare37129 (p : Pattern) (guard : d1547 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37128 p hg
    simpa only [d1547, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d1547, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37130 (p : Pattern) (guard : d39244 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37129 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37131 (p : Pattern) (guard : d258107 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37130 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37132 (p : Pattern) (guard : d258108 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37131 p hg
    simpa only [d258108, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d258108, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37133 (p : Pattern) (guard : d316775 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36487 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37132 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37134 (p : Pattern) (guard : d316776 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316775 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37133 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37135 (p : Pattern) (guard : d316777 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316776 p = 1 := by simpa only [d316777, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37134 p hg
    simpa only [d316777, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316777, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d316777, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37136 (p : Pattern) (guard : d316784 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36506 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37135 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37137 (p : Pattern) (guard : d316785 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316784 p = 1 := by simpa only [d316785, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37136 p hg
    simpa only [d316785, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316785, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316785, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37138 (p : Pattern) (guard : d316786 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316785 p = 1 := by simpa only [d316786, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37137 p hg
    simpa only [d316786, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316786, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316786, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37139 (p : Pattern) (guard : d316967 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316966 p = 1 := by simpa only [d316967, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37127 p hg
    simpa only [d316967, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316786 p = 1 := by simpa only [d316967, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37138 p hg
    simpa only [d316967, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37140 (p : Pattern) (guard : d316968 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316967 p = 1 := by simpa only [d316968, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37139 p hg
    simpa only [d316968, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316968, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316968, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37141 (p : Pattern) (guard : d316969 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316964 p = 1 := by simpa only [d316969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37115 p hg
    simpa only [d316969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316968 p = 1 := by simpa only [d316969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37140 p hg
    simpa only [d316969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37142 (p : Pattern) (guard : d316970 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316960 p = 1 := by simpa only [d316970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37106 p hg
    simpa only [d316970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316969 p = 1 := by simpa only [d316970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37141 p hg
    simpa only [d316970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37143 (p : Pattern) (guard : d40834 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare37144 (p : Pattern) (guard : d317691 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40834 p = 1 := by simpa only [d317691, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37143 p hg
    simpa only [d317691, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317691, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d317691, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37145 (p : Pattern) (guard : d317692 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317691 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37144 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37146 (p : Pattern) (guard : d317693 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317692 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37145 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37147 (p : Pattern) (guard : d317694 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317693 p = 1 := by simpa only [d317694, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37146 p hg
    simpa only [d317694, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317694, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d317694, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37148 (p : Pattern) (guard : d317695 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317694 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37147 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37149 (p : Pattern) (guard : d316767 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35908 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37120 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37150 (p : Pattern) (guard : d317696 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317695 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37148 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316767 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37149 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37151 (p : Pattern) (guard : d317697 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317696 p = 1 := by simpa only [d317697, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37150 p hg
    simpa only [d317697, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317697, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d317697, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37152 (p : Pattern) (guard : d317698 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36458 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317697 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37151 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37153 (p : Pattern) (guard : d317873 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317698 p = 1 := by simpa only [d317873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37152 p hg
    simpa only [d317873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37154 (p : Pattern) (guard : d317699 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317698 p = 1 := by simpa only [d317699, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36683 p hg
    simpa only [d317699, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317699, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317699, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37155 (p : Pattern) (guard : d317874 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317873 p = 1 := by simpa only [d317874, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37153 p hg
    simpa only [d317874, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317699 p = 1 := by simpa only [d317874, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37154 p hg
    simpa only [d317874, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37156 (p : Pattern) (guard : d40834 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare37157 (p : Pattern) (guard : d317691 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40834 p = 1 := by simpa only [d317691, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37156 p hg
    simpa only [d317691, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317691, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d317691, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37158 (p : Pattern) (guard : d317692 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317691 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37157 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37159 (p : Pattern) (guard : d317693 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317692 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37158 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37160 (p : Pattern) (guard : d317694 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317693 p = 1 := by simpa only [d317694, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37159 p hg
    simpa only [d317694, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317694, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d317694, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37161 (p : Pattern) (guard : d317695 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317694 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37160 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37162 (p : Pattern) (guard : d316767 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35921 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37132 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37163 (p : Pattern) (guard : d317696 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317695 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37161 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316767 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37162 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37164 (p : Pattern) (guard : d317697 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317696 p = 1 := by simpa only [d317697, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37163 p hg
    simpa only [d317697, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317697, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d317697, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37165 (p : Pattern) (guard : d317698 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36465 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317697 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37164 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37166 (p : Pattern) (guard : d317699 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317698 p = 1 := by simpa only [d317699, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37165 p hg
    simpa only [d317699, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317699, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317699, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37167 (p : Pattern) (guard : d317700 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317699 p = 1 := by simpa only [d317700, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37166 p hg
    simpa only [d317700, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317700, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317700, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37168 (p : Pattern) (guard : d317875 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317874 p = 1 := by simpa only [d317875, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37155 p hg
    simpa only [d317875, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317700 p = 1 := by simpa only [d317875, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37167 p hg
    simpa only [d317875, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37169 (p : Pattern) (guard : d317876 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317875 p = 1 := by simpa only [d317876, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37168 p hg
    simpa only [d317876, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317876, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317876, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37170 (p : Pattern) (guard : d317703 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37151 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37123 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37171 (p : Pattern) (guard : d317877 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317703 p = 1 := by simpa only [d317877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37170 p hg
    simpa only [d317877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37172 (p : Pattern) (guard : d317704 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317703 p = 1 := by simpa only [d317704, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36691 p hg
    simpa only [d317704, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317704, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317704, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37173 (p : Pattern) (guard : d317878 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317877 p = 1 := by simpa only [d317878, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37171 p hg
    simpa only [d317878, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317704 p = 1 := by simpa only [d317878, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37172 p hg
    simpa only [d317878, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37174 (p : Pattern) (guard : d317703 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37164 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37135 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37175 (p : Pattern) (guard : d317704 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317703 p = 1 := by simpa only [d317704, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37174 p hg
    simpa only [d317704, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317704, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317704, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37176 (p : Pattern) (guard : d317705 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317704 p = 1 := by simpa only [d317705, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37175 p hg
    simpa only [d317705, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317705, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317705, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37177 (p : Pattern) (guard : d317879 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317878 p = 1 := by simpa only [d317879, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37173 p hg
    simpa only [d317879, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317705 p = 1 := by simpa only [d317879, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37176 p hg
    simpa only [d317879, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37178 (p : Pattern) (guard : d317880 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317879 p = 1 := by simpa only [d317880, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37177 p hg
    simpa only [d317880, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317880, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317880, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37179 (p : Pattern) (guard : d317881 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317876 p = 1 := by simpa only [d317881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37169 p hg
    simpa only [d317881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317880 p = 1 := by simpa only [d317881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37178 p hg
    simpa only [d317881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37180 (p : Pattern) (guard : d317709 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37147 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37120 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37181 (p : Pattern) (guard : d258109 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37120 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37182 (p : Pattern) (guard : d317710 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317709 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37180 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37181 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37183 (p : Pattern) (guard : d317711 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317710 p = 1 := by simpa only [d317711, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37182 p hg
    simpa only [d317711, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317711, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d317711, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37184 (p : Pattern) (guard : d317712 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317711 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37183 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37185 (p : Pattern) (guard : d317882 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317712 p = 1 := by simpa only [d317882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37184 p hg
    simpa only [d317882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37186 (p : Pattern) (guard : d317713 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317712 p = 1 := by simpa only [d317713, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36706 p hg
    simpa only [d317713, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317713, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317713, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37187 (p : Pattern) (guard : d317883 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317882 p = 1 := by simpa only [d317883, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37185 p hg
    simpa only [d317883, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317713 p = 1 := by simpa only [d317883, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37186 p hg
    simpa only [d317883, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37188 (p : Pattern) (guard : d317709 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37160 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37132 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37189 (p : Pattern) (guard : d258109 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37132 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37190 (p : Pattern) (guard : d317710 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317709 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37188 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37189 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37191 (p : Pattern) (guard : d317711 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317710 p = 1 := by simpa only [d317711, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37190 p hg
    simpa only [d317711, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317711, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d317711, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37192 (p : Pattern) (guard : d317712 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317711 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37191 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37193 (p : Pattern) (guard : d317713 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317712 p = 1 := by simpa only [d317713, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37192 p hg
    simpa only [d317713, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317713, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317713, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37194 (p : Pattern) (guard : d317714 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317713 p = 1 := by simpa only [d317714, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37193 p hg
    simpa only [d317714, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317714, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317714, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37195 (p : Pattern) (guard : d317884 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317883 p = 1 := by simpa only [d317884, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37187 p hg
    simpa only [d317884, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317714 p = 1 := by simpa only [d317884, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37194 p hg
    simpa only [d317884, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37196 (p : Pattern) (guard : d317885 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317884 p = 1 := by simpa only [d317885, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37195 p hg
    simpa only [d317885, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317885, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317885, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37197 (p : Pattern) (guard : d317886 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316968 p = 1 := by simpa only [d317886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37140 p hg
    simpa only [d317886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317885 p = 1 := by simpa only [d317886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37196 p hg
    simpa only [d317886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37198 (p : Pattern) (guard : d317887 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317881 p = 1 := by simpa only [d317887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37179 p hg
    simpa only [d317887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317886 p = 1 := by simpa only [d317887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37197 p hg
    simpa only [d317887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37199 (p : Pattern) (guard : d317888 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316970 p = 1 := by simpa only [d317888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37142 p hg
    simpa only [d317888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317887 p = 1 := by simpa only [d317888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37198 p hg
    simpa only [d317888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37200 (p : Pattern) (guard : d317889 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317889, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317889, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317888 p = 1 := by simpa only [d317889, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37199 p hg
    simpa only [d317889, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37201 (p : Pattern) (guard : d317890 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317890, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317890, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317889 p = 1 := by simpa only [d317890, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37200 p hg
    simpa only [d317890, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37202 (p : Pattern) (guard : d317891 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317885 p = 1 := by simpa only [d317891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37196 p hg
    simpa only [d317891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37203 (p : Pattern) (guard : d317892 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317886 p = 1 := by simpa only [d317892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37197 p hg
    simpa only [d317892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317891 p = 1 := by simpa only [d317892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37202 p hg
    simpa only [d317892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37204 (p : Pattern) (guard : d317893 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317887 p = 1 := by simpa only [d317893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37198 p hg
    simpa only [d317893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317892 p = 1 := by simpa only [d317893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37203 p hg
    simpa only [d317893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37205 (p : Pattern) (guard : d317894 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317894, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317894, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317893 p = 1 := by simpa only [d317894, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37204 p hg
    simpa only [d317894, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37206 (p : Pattern) (guard : d317895 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317895, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317895, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317894 p = 1 := by simpa only [d317895, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37205 p hg
    simpa only [d317895, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37207 (p : Pattern) (guard : d317896 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317890 p = 1 := by simpa only [d317896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37201 p hg
    simpa only [d317896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317895 p = 1 := by simpa only [d317896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37206 p hg
    simpa only [d317896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37208 (p : Pattern) (guard : d317719 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37147 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37209 (p : Pattern) (guard : d317720 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317719 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37208 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37181 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37210 (p : Pattern) (guard : d317721 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317720 p = 1 := by simpa only [d317721, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37209 p hg
    simpa only [d317721, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317721, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d317721, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37211 (p : Pattern) (guard : d317722 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37151 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317721 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37210 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37212 (p : Pattern) (guard : d317897 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317722 p = 1 := by simpa only [d317897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37211 p hg
    simpa only [d317897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37213 (p : Pattern) (guard : d317723 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317722 p = 1 := by simpa only [d317723, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36716 p hg
    simpa only [d317723, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317723, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317723, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37214 (p : Pattern) (guard : d317898 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317897 p = 1 := by simpa only [d317898, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37212 p hg
    simpa only [d317898, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317723 p = 1 := by simpa only [d317898, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37213 p hg
    simpa only [d317898, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37215 (p : Pattern) (guard : d317719 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37160 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37216 (p : Pattern) (guard : d317720 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317719 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37215 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37189 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37217 (p : Pattern) (guard : d317721 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317720 p = 1 := by simpa only [d317721, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37216 p hg
    simpa only [d317721, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317721, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d317721, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37218 (p : Pattern) (guard : d317722 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37164 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317721 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37217 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37219 (p : Pattern) (guard : d317723 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317722 p = 1 := by simpa only [d317723, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37218 p hg
    simpa only [d317723, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317723, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317723, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37220 (p : Pattern) (guard : d317724 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317723 p = 1 := by simpa only [d317724, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37219 p hg
    simpa only [d317724, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317724, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317724, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37221 (p : Pattern) (guard : d317899 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317898 p = 1 := by simpa only [d317899, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37214 p hg
    simpa only [d317899, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317724 p = 1 := by simpa only [d317899, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37220 p hg
    simpa only [d317899, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37222 (p : Pattern) (guard : d317900 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317899 p = 1 := by simpa only [d317900, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37221 p hg
    simpa only [d317900, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317900, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317900, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37223 (p : Pattern) (guard : d317727 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317721 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37210 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37224 (p : Pattern) (guard : d317901 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317727 p = 1 := by simpa only [d317901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37223 p hg
    simpa only [d317901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37225 (p : Pattern) (guard : d317728 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317727 p = 1 := by simpa only [d317728, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36721 p hg
    simpa only [d317728, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317728, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317728, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37226 (p : Pattern) (guard : d317902 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317901 p = 1 := by simpa only [d317902, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37224 p hg
    simpa only [d317902, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317728 p = 1 := by simpa only [d317902, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37225 p hg
    simpa only [d317902, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37227 (p : Pattern) (guard : d317727 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317721 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37217 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37228 (p : Pattern) (guard : d317728 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317727 p = 1 := by simpa only [d317728, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37227 p hg
    simpa only [d317728, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317728, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317728, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37229 (p : Pattern) (guard : d317729 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317728 p = 1 := by simpa only [d317729, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37228 p hg
    simpa only [d317729, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317729, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317729, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37230 (p : Pattern) (guard : d317903 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317902 p = 1 := by simpa only [d317903, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37226 p hg
    simpa only [d317903, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317729 p = 1 := by simpa only [d317903, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37229 p hg
    simpa only [d317903, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37231 (p : Pattern) (guard : d317904 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317903 p = 1 := by simpa only [d317904, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37230 p hg
    simpa only [d317904, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317904, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317904, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37232 (p : Pattern) (guard : d317905 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317900 p = 1 := by simpa only [d317905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37222 p hg
    simpa only [d317905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317904 p = 1 := by simpa only [d317905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37231 p hg
    simpa only [d317905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37233 (p : Pattern) (guard : d317906 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317905 p = 1 := by simpa only [d317906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37232 p hg
    simpa only [d317906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317891 p = 1 := by simpa only [d317906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37202 p hg
    simpa only [d317906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37234 (p : Pattern) (guard : d317907 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317887 p = 1 := by simpa only [d317907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37198 p hg
    simpa only [d317907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317906 p = 1 := by simpa only [d317907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37233 p hg
    simpa only [d317907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37235 (p : Pattern) (guard : d317908 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317908, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317908, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317907 p = 1 := by simpa only [d317908, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37234 p hg
    simpa only [d317908, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37236 (p : Pattern) (guard : d317909 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317909, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317909, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317908 p = 1 := by simpa only [d317909, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37235 p hg
    simpa only [d317909, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37237 (p : Pattern) (guard : d317910 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317904 p = 1 := by simpa only [d317910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37231 p hg
    simpa only [d317910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37238 (p : Pattern) (guard : d317911 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317910 p = 1 := by simpa only [d317911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37237 p hg
    simpa only [d317911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37239 (p : Pattern) (guard : d317912 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317906 p = 1 := by simpa only [d317912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37233 p hg
    simpa only [d317912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317911 p = 1 := by simpa only [d317912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37238 p hg
    simpa only [d317912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37240 (p : Pattern) (guard : d317913 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317913, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317913, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317912 p = 1 := by simpa only [d317913, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37239 p hg
    simpa only [d317913, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37241 (p : Pattern) (guard : d317914 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317914, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317914, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317913 p = 1 := by simpa only [d317914, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37240 p hg
    simpa only [d317914, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37242 (p : Pattern) (guard : d317915 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317909 p = 1 := by simpa only [d317915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37236 p hg
    simpa only [d317915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317914 p = 1 := by simpa only [d317915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37241 p hg
    simpa only [d317915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37243 (p : Pattern) (guard : d317916 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317896 p = 1 := by simpa only [d317916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37207 p hg
    simpa only [d317916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317915 p = 1 := by simpa only [d317916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37242 p hg
    simpa only [d317916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37244 (p : Pattern) (guard : d317917 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317916 p = 1 := by simpa only [d317917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37243 p hg
    simpa only [d317917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37245 (p : Pattern) (guard : d317918 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317917 p = 1 := by simpa only [d317918, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37244 p hg
    simpa only [d317918, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317918, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d317918, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37246 (p : Pattern) (guard : d317919 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317919, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317919, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317918 p = 1 := by simpa only [d317919, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37245 p hg
    simpa only [d317919, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37247 (p : Pattern) (guard : d317920 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317914 p = 1 := by simpa only [d317920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37241 p hg
    simpa only [d317920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37248 (p : Pattern) (guard : d317921 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317915 p = 1 := by simpa only [d317921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37242 p hg
    simpa only [d317921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317920 p = 1 := by simpa only [d317921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37247 p hg
    simpa only [d317921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37249 (p : Pattern) (guard : d317922 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317921 p = 1 := by simpa only [d317922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37248 p hg
    simpa only [d317922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317922, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
