import NetHack.Soko22Hazard87.Compare186
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46750 (p : Pattern) (guard : d275532 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275531 p = 1 := by simpa only [d275532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46749 p hg
    simpa only [d275532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46751 (p : Pattern) (guard : d275533 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275532 p = 1 := by simpa only [d275533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46750 p hg
    simpa only [d275533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46752 (p : Pattern) (guard : d275534 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275533 p = 1 := by simpa only [d275534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46751 p hg
    simpa only [d275534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46753 (p : Pattern) (guard : d275540 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275540, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275540, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275534 p = 1 := by simpa only [d275540, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46752 p hg
    simpa only [d275540, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46754 (p : Pattern) (guard : d275541 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d275541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275540 p = 1 := by simpa only [d275541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46753 p hg
    simpa only [d275541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46755 (p : Pattern) (guard : d275542 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d275541 p = 1 := by simpa only [d275542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46754 p hg
    simpa only [d275542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d275542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46756 (p : Pattern) (guard : d275543 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d275542 p = 1 := by simpa only [d275543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46755 p hg
    simpa only [d275543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d275543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46757 (p : Pattern) (guard : d275544 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d275543 p = 1 := by simpa only [d275544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46756 p hg
    simpa only [d275544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d275544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46758 (p : Pattern) (guard : d275545 p = 1) : d50676 p ≤ (1 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d275539 p = 1 := by simpa only [d275545, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46704 p hg
    simpa only [d275545, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275544 p = 1 := by simpa only [d275545, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46757 p hg
    simpa only [d275545, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46759 (p : Pattern) (guard : d0 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46760 (p : Pattern) (guard : d0 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46761 (p : Pattern) (guard : d0 p = 1) : d50712 p ≤ (1 : Int) + d367901 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46762 (p : Pattern) (guard : d0 p = 1) : d50724 p ≤ (1 : Int) + d367910 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46763 (p : Pattern) (guard : d0 p = 1) : d50725 p ≤ (1 : Int) + d367780 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46764 (p : Pattern) (guard : d45587 p = 1) : d47630 p ≤ (1 : Int) + d47630 p := by
  omega
theorem compare46765 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (1 : Int) + d49310 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46766 (p : Pattern) (guard : d46472 p = 1) : d47630 p ≤ (1 : Int) + d49311 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46764 p hg
    simpa only [d46472, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46765 p hg
    simpa only [d46472, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46767 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (1 : Int) + d49315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46768 (p : Pattern) (guard : d46473 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46472 p = 1 := by simpa only [d46473, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46766 p hg
    simpa only [d46473, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46473, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46767 p hg
    simpa only [d46473, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46769 (p : Pattern) (guard : d46477 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46473 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46768 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46770 (p : Pattern) (guard : d0 p = 1) : d49316 p ≤ (1 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46771 (p : Pattern) (guard : d179204 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46477 p = 1 := by simpa only [d179204, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46769 p hg
    simpa only [d179204, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179204, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46770 p hg
    simpa only [d179204, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46772 (p : Pattern) (guard : d275501 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d179204 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46771 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46773 (p : Pattern) (guard : d275502 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d275501 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46772 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46774 (p : Pattern) (guard : d0 p = 1) : d49317 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46775 (p : Pattern) (guard : d275503 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d275502 p = 1 := by simpa only [d275503, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46773 p hg
    simpa only [d275503, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275503, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46774 p hg
    simpa only [d275503, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46776 (p : Pattern) (guard : d0 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46777 (p : Pattern) (guard : d275504 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d275503 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46775 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46776 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46778 (p : Pattern) (guard : d275546 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275546, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d275546, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275504 p = 1 := by simpa only [d275546, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46777 p hg
    simpa only [d275546, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46779 (p : Pattern) (guard : d275505 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d275504 p = 1 := by simpa only [d275505, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46663 p hg
    simpa only [d275505, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275505, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d275505, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46780 (p : Pattern) (guard : d275547 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d275546 p = 1 := by simpa only [d275547, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46778 p hg
    simpa only [d275547, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275505 p = 1 := by simpa only [d275547, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46779 p hg
    simpa only [d275547, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46781 (p : Pattern) (guard : d45587 p = 1) : d47634 p ≤ (1 : Int) + d47634 p := by
  omega
theorem compare46782 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (1 : Int) + d47963 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46783 (p : Pattern) (guard : d46472 p = 1) : d47634 p ≤ (1 : Int) + d49319 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46781 p hg
    simpa only [d46472, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46782 p hg
    simpa only [d46472, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46784 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (1 : Int) + d49322 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46785 (p : Pattern) (guard : d46473 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46472 p = 1 := by simpa only [d46473, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46783 p hg
    simpa only [d46473, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46473, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46784 p hg
    simpa only [d46473, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46786 (p : Pattern) (guard : d46477 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46473 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46785 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46787 (p : Pattern) (guard : d0 p = 1) : d49323 p ≤ (1 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46788 (p : Pattern) (guard : d179204 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46477 p = 1 := by simpa only [d179204, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46786 p hg
    simpa only [d179204, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179204, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46787 p hg
    simpa only [d179204, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46789 (p : Pattern) (guard : d275501 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d179204 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46788 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46790 (p : Pattern) (guard : d275502 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d275501 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46789 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46791 (p : Pattern) (guard : d0 p = 1) : d49324 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46792 (p : Pattern) (guard : d275503 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d275502 p = 1 := by simpa only [d275503, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46790 p hg
    simpa only [d275503, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275503, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46791 p hg
    simpa only [d275503, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46793 (p : Pattern) (guard : d0 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46794 (p : Pattern) (guard : d275504 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d275503 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46792 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46793 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46795 (p : Pattern) (guard : d275505 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d275504 p = 1 := by simpa only [d275505, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46794 p hg
    simpa only [d275505, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275505, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d275505, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46796 (p : Pattern) (guard : d275506 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d275505 p = 1 := by simpa only [d275506, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46795 p hg
    simpa only [d275506, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275506, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d275506, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46797 (p : Pattern) (guard : d275548 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d275547 p = 1 := by simpa only [d275548, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46780 p hg
    simpa only [d275548, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275506 p = 1 := by simpa only [d275548, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46796 p hg
    simpa only [d275548, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46798 (p : Pattern) (guard : d0 p = 1) : d50732 p ≤ (1 : Int) + d367916 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46799 (p : Pattern) (guard : d275549 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d275548 p = 1 := by simpa only [d275549, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46797 p hg
    simpa only [d275549, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275549, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d275549, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46800 (p : Pattern) (guard : d0 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46801 (p : Pattern) (guard : d275550 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d275549 p = 1 := by simpa only [d275550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46799 p hg
    simpa only [d275550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46800 p hg
    simpa only [d275550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46802 (p : Pattern) (guard : d275551 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d275550 p = 1 := by simpa only [d275551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46801 p hg
    simpa only [d275551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46800 p hg
    simpa only [d275551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46803 (p : Pattern) (guard : d275552 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d275551 p = 1 := by simpa only [d275552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46802 p hg
    simpa only [d275552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46800 p hg
    simpa only [d275552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46804 (p : Pattern) (guard : d275553 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275553, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d275553, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275552 p = 1 := by simpa only [d275553, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46803 p hg
    simpa only [d275553, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46805 (p : Pattern) (guard : d275554 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275554, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d275554, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275553 p = 1 := by simpa only [d275554, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46804 p hg
    simpa only [d275554, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46806 (p : Pattern) (guard : d0 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46807 (p : Pattern) (guard : d275555 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d275554 p = 1 := by simpa only [d275555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46805 p hg
    simpa only [d275555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d275555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46808 (p : Pattern) (guard : d275556 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d275555 p = 1 := by simpa only [d275556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46807 p hg
    simpa only [d275556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d275556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46809 (p : Pattern) (guard : d275557 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d275556 p = 1 := by simpa only [d275557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46808 p hg
    simpa only [d275557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d275557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46810 (p : Pattern) (guard : d0 p = 1) : d50736 p ≤ (1 : Int) + d367920 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46811 (p : Pattern) (guard : d275558 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d275557 p = 1 := by simpa only [d275558, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46809 p hg
    simpa only [d275558, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275558, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d275558, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46812 (p : Pattern) (guard : d275559 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275559, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d275559, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275558 p = 1 := by simpa only [d275559, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46811 p hg
    simpa only [d275559, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46813 (p : Pattern) (guard : d275560 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d275559 p = 1 := by simpa only [d275560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46812 p hg
    simpa only [d275560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46814 (p : Pattern) (guard : d275561 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d275560 p = 1 := by simpa only [d275561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46813 p hg
    simpa only [d275561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46815 (p : Pattern) (guard : d275562 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d275561 p = 1 := by simpa only [d275562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46814 p hg
    simpa only [d275562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46816 (p : Pattern) (guard : d275563 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d275562 p = 1 := by simpa only [d275563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46815 p hg
    simpa only [d275563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46817 (p : Pattern) (guard : d275564 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275563 p = 1 := by simpa only [d275564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46816 p hg
    simpa only [d275564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46818 (p : Pattern) (guard : d275565 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d275564 p = 1 := by simpa only [d275565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46817 p hg
    simpa only [d275565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46819 (p : Pattern) (guard : d275566 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275565 p = 1 := by simpa only [d275566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46818 p hg
    simpa only [d275566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46820 (p : Pattern) (guard : d275567 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275566 p = 1 := by simpa only [d275567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46819 p hg
    simpa only [d275567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46821 (p : Pattern) (guard : d275568 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275567 p = 1 := by simpa only [d275568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46820 p hg
    simpa only [d275568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46822 (p : Pattern) (guard : d275569 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275569, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275569, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275568 p = 1 := by simpa only [d275569, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46821 p hg
    simpa only [d275569, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46823 (p : Pattern) (guard : d275570 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d275570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275569 p = 1 := by simpa only [d275570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46822 p hg
    simpa only [d275570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46824 (p : Pattern) (guard : d275571 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d275570 p = 1 := by simpa only [d275571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46823 p hg
    simpa only [d275571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d275571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46825 (p : Pattern) (guard : d275572 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d275571 p = 1 := by simpa only [d275572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46824 p hg
    simpa only [d275572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d275572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46826 (p : Pattern) (guard : d275573 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d275572 p = 1 := by simpa only [d275573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46825 p hg
    simpa only [d275573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d275573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46827 (p : Pattern) (guard : d0 p = 1) : d50821 p ≤ (1 : Int) + d367983 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46828 (p : Pattern) (guard : d275574 p = 1) : d50822 p ≤ (1 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d275573 p = 1 := by simpa only [d275574, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46826 p hg
    simpa only [d275574, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275574, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46827 p hg
    simpa only [d275574, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46829 (p : Pattern) (guard : d275575 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d275545 p = 1 := by simpa only [d275575, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46758 p hg
    simpa only [d275575, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275574 p = 1 := by simpa only [d275575, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46828 p hg
    simpa only [d275575, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46830 (p : Pattern) (guard : d275576 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d275576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275575 p = 1 := by simpa only [d275576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46829 p hg
    simpa only [d275576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46831 (p : Pattern) (guard : d275577 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d275577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275576 p = 1 := by simpa only [d275577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46830 p hg
    simpa only [d275577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46832 (p : Pattern) (guard : d275578 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d275578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275577 p = 1 := by simpa only [d275578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46831 p hg
    simpa only [d275578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46833 (p : Pattern) (guard : d275579 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d275579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275578 p = 1 := by simpa only [d275579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46832 p hg
    simpa only [d275579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46834 (p : Pattern) (guard : d275580 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d275580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275579 p = 1 := by simpa only [d275580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46833 p hg
    simpa only [d275580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46835 (p : Pattern) (guard : d275581 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275523 p = 1 := by simpa only [d275581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46688 p hg
    simpa only [d275581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46836 (p : Pattern) (guard : d275582 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275581 p = 1 := by simpa only [d275582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46835 p hg
    simpa only [d275582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46837 (p : Pattern) (guard : d275583 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275582 p = 1 := by simpa only [d275583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46836 p hg
    simpa only [d275583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46838 (p : Pattern) (guard : d275584 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275583 p = 1 := by simpa only [d275584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46837 p hg
    simpa only [d275584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46839 (p : Pattern) (guard : d275585 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275584 p = 1 := by simpa only [d275585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46838 p hg
    simpa only [d275585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46840 (p : Pattern) (guard : d275586 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275585 p = 1 := by simpa only [d275586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46839 p hg
    simpa only [d275586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46841 (p : Pattern) (guard : d275587 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d275586 p = 1 := by simpa only [d275587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46840 p hg
    simpa only [d275587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46842 (p : Pattern) (guard : d275588 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275530 p = 1 := by simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46695 p hg
    simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46843 (p : Pattern) (guard : d275589 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275588 p = 1 := by simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46842 p hg
    simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46844 (p : Pattern) (guard : d275590 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275589 p = 1 := by simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46843 p hg
    simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46845 (p : Pattern) (guard : d275591 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275590 p = 1 := by simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46844 p hg
    simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46846 (p : Pattern) (guard : d275592 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d275584 p = 1 := by simpa only [d275592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46838 p hg
    simpa only [d275592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275591 p = 1 := by simpa only [d275592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46845 p hg
    simpa only [d275592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46847 (p : Pattern) (guard : d275593 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d275585 p = 1 := by simpa only [d275593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46839 p hg
    simpa only [d275593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275592 p = 1 := by simpa only [d275593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46846 p hg
    simpa only [d275593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46848 (p : Pattern) (guard : d275594 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d275593 p = 1 := by simpa only [d275594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46847 p hg
    simpa only [d275594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46849 (p : Pattern) (guard : d275595 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d275587 p = 1 := by simpa only [d275595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46841 p hg
    simpa only [d275595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275594 p = 1 := by simpa only [d275595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46848 p hg
    simpa only [d275595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46850 (p : Pattern) (guard : d275596 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275520 p = 1 := by simpa only [d275596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46685 p hg
    simpa only [d275596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46851 (p : Pattern) (guard : d275597 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275596 p = 1 := by simpa only [d275597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46850 p hg
    simpa only [d275597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46852 (p : Pattern) (guard : d275598 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275597 p = 1 := by simpa only [d275598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46851 p hg
    simpa only [d275598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46853 (p : Pattern) (guard : d275599 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275598 p = 1 := by simpa only [d275599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46852 p hg
    simpa only [d275599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46854 (p : Pattern) (guard : d275600 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275599 p = 1 := by simpa only [d275600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46853 p hg
    simpa only [d275600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46855 (p : Pattern) (guard : d275601 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275600 p = 1 := by simpa only [d275601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46854 p hg
    simpa only [d275601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46856 (p : Pattern) (guard : d275602 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275519 p = 1 := by simpa only [d275602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46684 p hg
    simpa only [d275602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46857 (p : Pattern) (guard : d275603 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d275602 p = 1 := by simpa only [d275603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46856 p hg
    simpa only [d275603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46858 (p : Pattern) (guard : d275604 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275603 p = 1 := by simpa only [d275604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46857 p hg
    simpa only [d275604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46859 (p : Pattern) (guard : d275605 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275604 p = 1 := by simpa only [d275605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46858 p hg
    simpa only [d275605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46860 (p : Pattern) (guard : d275606 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275605 p = 1 := by simpa only [d275606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46859 p hg
    simpa only [d275606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46861 (p : Pattern) (guard : d275607 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275606 p = 1 := by simpa only [d275607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46860 p hg
    simpa only [d275607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46862 (p : Pattern) (guard : d44996 p = 1) : d47617 p ≤ (1 : Int) + d47617 p := by
  omega
theorem compare46863 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (1 : Int) + d49390 p := by
  have ha := bounds4 p
  have hb := bounds49390 p
  omega
theorem compare46864 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (1 : Int) + d47656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46865 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (1 : Int) + d49391 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, d49391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46863 p hg
    simpa only [d15, d47617, d49391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, d49391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46864 p hg
    simpa only [d15, d47617, d49391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46866 (p : Pattern) (guard : d45587 p = 1) : d47617 p ≤ (1 : Int) + d49391 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46651 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46865 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46867 (p : Pattern) (guard : d45588 p = 1) : d47617 p ≤ (1 : Int) + d49392 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d45588, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46862 p hg
    simpa only [d45588, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d45588, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46866 p hg
    simpa only [d45588, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46868 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (1 : Int) + d49394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46869 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (1 : Int) + d49393 p := by
  have ha := bounds4 p
  have hb := bounds49393 p
  omega
theorem compare46870 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (1 : Int) + d47789 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46871 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (1 : Int) + d49394 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, d49394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46869 p hg
    simpa only [d15, d47617, d49394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, d49394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46870 p hg
    simpa only [d15, d47617, d49394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46872 (p : Pattern) (guard : d45587 p = 1) : d47617 p ≤ (1 : Int) + d49394 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46868 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46871 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46873 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (1 : Int) + d47938 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46874 (p : Pattern) (guard : d46472 p = 1) : d47617 p ≤ (1 : Int) + d49395 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46872 p hg
    simpa only [d46472, d49395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46873 p hg
    simpa only [d46472, d49395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46875 (p : Pattern) (guard : d369384 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d45588 p = 1 := by simpa only [d369384, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46867 p hg
    simpa only [d369384, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46472 p = 1 := by simpa only [d369384, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46874 p hg
    simpa only [d369384, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46876 (p : Pattern) (guard : d369385 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 223 with
  | false =>
    have hg : d369384 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46875 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46877 (p : Pattern) (guard : d369386 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369385 p = 1 := by simpa only [d369386, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46876 p hg
    simpa only [d369386, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369386, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46656 p hg
    simpa only [d369386, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46878 (p : Pattern) (guard : d369387 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369386 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46877 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46657 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46879 (p : Pattern) (guard : d369388 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46878 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275501 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46658 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46880 (p : Pattern) (guard : d369389 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369388 p = 1 := by simpa only [d369389, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46879 p hg
    simpa only [d369389, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369389, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46660 p hg
    simpa only [d369389, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46881 (p : Pattern) (guard : d369390 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46880 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46661 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46882 (p : Pattern) (guard : d369391 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369390 p = 1 := by simpa only [d369391, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46881 p hg
    simpa only [d369391, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369391, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369391, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46883 (p : Pattern) (guard : d369392 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369391 p = 1 := by simpa only [d369392, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46882 p hg
    simpa only [d369392, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369392, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369392, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46884 (p : Pattern) (guard : d369393 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369393, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369393, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369392 p = 1 := by simpa only [d369393, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46883 p hg
    simpa only [d369393, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46885 (p : Pattern) (guard : d369394 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369393 p = 1 := by simpa only [d369394, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46884 p hg
    simpa only [d369394, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369394, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369394, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46886 (p : Pattern) (guard : d369395 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369394 p = 1 := by simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46885 p hg
    simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275508 p = 1 := by simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46670 p hg
    simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46887 (p : Pattern) (guard : d369396 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369395 p = 1 := by simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46886 p hg
    simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275509 p = 1 := by simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46888 (p : Pattern) (guard : d369397 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369396 p = 1 := by simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46887 p hg
    simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275510 p = 1 := by simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46673 p hg
    simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46889 (p : Pattern) (guard : d369398 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369398, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d369398, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369397 p = 1 := by simpa only [d369398, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46888 p hg
    simpa only [d369398, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46890 (p : Pattern) (guard : d369399 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369399, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d369399, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369398 p = 1 := by simpa only [d369399, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46889 p hg
    simpa only [d369399, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46891 (p : Pattern) (guard : d369400 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369399 p = 1 := by simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46890 p hg
    simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275513 p = 1 := by simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46676 p hg
    simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46892 (p : Pattern) (guard : d369401 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369400 p = 1 := by simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46891 p hg
    simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275514 p = 1 := by simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46678 p hg
    simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46893 (p : Pattern) (guard : d369402 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369401 p = 1 := by simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46892 p hg
    simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46894 (p : Pattern) (guard : d369403 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369402 p = 1 := by simpa only [d369403, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46893 p hg
    simpa only [d369403, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369403, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d369403, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46895 (p : Pattern) (guard : d369404 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369404, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369404, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369403 p = 1 := by simpa only [d369404, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46894 p hg
    simpa only [d369404, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46896 (p : Pattern) (guard : d369405 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369404 p = 1 := by simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46895 p hg
    simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275518 p = 1 := by simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46683 p hg
    simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46897 (p : Pattern) (guard : d369406 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369405 p = 1 := by simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46896 p hg
    simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46898 (p : Pattern) (guard : d369407 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369406 p = 1 := by simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46897 p hg
    simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46899 (p : Pattern) (guard : d369408 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369407 p = 1 := by simpa only [d369408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46898 p hg
    simpa only [d369408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46900 (p : Pattern) (guard : d369409 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369408 p = 1 := by simpa only [d369409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46899 p hg
    simpa only [d369409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275522 p = 1 := by simpa only [d369409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46687 p hg
    simpa only [d369409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46901 (p : Pattern) (guard : d369410 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369409 p = 1 := by simpa only [d369410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46900 p hg
    simpa only [d369410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46902 (p : Pattern) (guard : d369411 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369410 p = 1 := by simpa only [d369411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46901 p hg
    simpa only [d369411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275524 p = 1 := by simpa only [d369411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46689 p hg
    simpa only [d369411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46903 (p : Pattern) (guard : d369412 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d275607 p = 1 := by simpa only [d369412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46861 p hg
    simpa only [d369412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369411 p = 1 := by simpa only [d369412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46902 p hg
    simpa only [d369412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46904 (p : Pattern) (guard : d369413 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d275601 p = 1 := by simpa only [d369413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46855 p hg
    simpa only [d369413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369412 p = 1 := by simpa only [d369413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46903 p hg
    simpa only [d369413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46905 (p : Pattern) (guard : d369414 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369413 p = 1 := by simpa only [d369414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46904 p hg
    simpa only [d369414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46906 (p : Pattern) (guard : d275641 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d275596 p = 1 := by simpa only [d275641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46850 p hg
    simpa only [d275641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46907 (p : Pattern) (guard : d275642 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275641 p = 1 := by simpa only [d275642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46906 p hg
    simpa only [d275642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46908 (p : Pattern) (guard : d275643 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275642 p = 1 := by simpa only [d275643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46907 p hg
    simpa only [d275643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46909 (p : Pattern) (guard : d275644 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275643 p = 1 := by simpa only [d275644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46908 p hg
    simpa only [d275644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46910 (p : Pattern) (guard : d275645 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275644 p = 1 := by simpa only [d275645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46909 p hg
    simpa only [d275645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46911 (p : Pattern) (guard : d275646 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d275603 p = 1 := by simpa only [d275646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46857 p hg
    simpa only [d275646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46912 (p : Pattern) (guard : d275647 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275646 p = 1 := by simpa only [d275647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46911 p hg
    simpa only [d275647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46913 (p : Pattern) (guard : d275648 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275647 p = 1 := by simpa only [d275648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46912 p hg
    simpa only [d275648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46914 (p : Pattern) (guard : d275649 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275648 p = 1 := by simpa only [d275649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46913 p hg
    simpa only [d275649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46915 (p : Pattern) (guard : d369415 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369407 p = 1 := by simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46898 p hg
    simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46916 (p : Pattern) (guard : d369416 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369415 p = 1 := by simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46915 p hg
    simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275529 p = 1 := by simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46694 p hg
    simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46917 (p : Pattern) (guard : d369417 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369416 p = 1 := by simpa only [d369417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46916 p hg
    simpa only [d369417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46918 (p : Pattern) (guard : d369418 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369417 p = 1 := by simpa only [d369418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46917 p hg
    simpa only [d369418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275531 p = 1 := by simpa only [d369418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46696 p hg
    simpa only [d369418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46919 (p : Pattern) (guard : d369419 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d275649 p = 1 := by simpa only [d369419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46914 p hg
    simpa only [d369419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369418 p = 1 := by simpa only [d369419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46918 p hg
    simpa only [d369419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46920 (p : Pattern) (guard : d369420 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d275645 p = 1 := by simpa only [d369420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46910 p hg
    simpa only [d369420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369419 p = 1 := by simpa only [d369420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46919 p hg
    simpa only [d369420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46921 (p : Pattern) (guard : d369421 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369413 p = 1 := by simpa only [d369421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46904 p hg
    simpa only [d369421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369420 p = 1 := by simpa only [d369421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46920 p hg
    simpa only [d369421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46922 (p : Pattern) (guard : d369422 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369414 p = 1 := by simpa only [d369422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46905 p hg
    simpa only [d369422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369421 p = 1 := by simpa only [d369422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46921 p hg
    simpa only [d369422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46923 (p : Pattern) (guard : d275658 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d275584 p = 1 := by simpa only [d275658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46838 p hg
    simpa only [d275658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46924 (p : Pattern) (guard : d275659 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d275658 p = 1 := by simpa only [d275659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46923 p hg
    simpa only [d275659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46925 (p : Pattern) (guard : d369423 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369422 p = 1 := by simpa only [d369423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46922 p hg
    simpa only [d369423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275659 p = 1 := by simpa only [d369423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46924 p hg
    simpa only [d369423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46926 (p : Pattern) (guard : d369424 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369423 p = 1 := by simpa only [d369424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46925 p hg
    simpa only [d369424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46927 (p : Pattern) (guard : d369425 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d275595 p = 1 := by simpa only [d369425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46849 p hg
    simpa only [d369425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369424 p = 1 := by simpa only [d369425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46926 p hg
    simpa only [d369425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46928 (p : Pattern) (guard : d44996 p = 1) : d47706 p ≤ (1 : Int) + d47706 p := by
  omega
theorem compare46929 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (1 : Int) + d49559 p := by
  have ha := bounds5 p
  have hb := bounds49559 p
  omega
theorem compare46930 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (1 : Int) + d47638 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46931 (p : Pattern) (guard : d15 p = 1) : d47706 p ≤ (1 : Int) + d49560 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47706, d49560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46929 p hg
    simpa only [d15, d47706, d49560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47706, d49560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46930 p hg
    simpa only [d15, d47706, d49560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46932 (p : Pattern) (guard : d45587 p = 1) : d47706 p ≤ (1 : Int) + d49560 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46712 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46931 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46933 (p : Pattern) (guard : d45588 p = 1) : d47706 p ≤ (1 : Int) + d49561 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d45588, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46928 p hg
    simpa only [d45588, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d45588, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46932 p hg
    simpa only [d45588, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46934 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (1 : Int) + d49563 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46935 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (1 : Int) + d49562 p := by
  have ha := bounds5 p
  have hb := bounds49562 p
  omega
theorem compare46936 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (1 : Int) + d47622 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46937 (p : Pattern) (guard : d15 p = 1) : d47706 p ≤ (1 : Int) + d49563 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47706, d49563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46935 p hg
    simpa only [d15, d47706, d49563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47706, d49563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46936 p hg
    simpa only [d15, d47706, d49563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46938 (p : Pattern) (guard : d45587 p = 1) : d47706 p ≤ (1 : Int) + d49563 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46934 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46937 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46939 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (1 : Int) + d47947 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46940 (p : Pattern) (guard : d46472 p = 1) : d47706 p ≤ (1 : Int) + d49564 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46938 p hg
    simpa only [d46472, d49564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46939 p hg
    simpa only [d46472, d49564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46941 (p : Pattern) (guard : d369384 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d45588 p = 1 := by simpa only [d369384, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46933 p hg
    simpa only [d369384, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46472 p = 1 := by simpa only [d369384, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46940 p hg
    simpa only [d369384, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46942 (p : Pattern) (guard : d369385 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 223 with
  | false =>
    have hg : d369384 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46941 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46943 (p : Pattern) (guard : d369386 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369385 p = 1 := by simpa only [d369386, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46942 p hg
    simpa only [d369386, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369386, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46717 p hg
    simpa only [d369386, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46944 (p : Pattern) (guard : d369387 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369386 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46943 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46718 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46945 (p : Pattern) (guard : d369388 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46944 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275501 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46946 (p : Pattern) (guard : d369389 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369388 p = 1 := by simpa only [d369389, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46945 p hg
    simpa only [d369389, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369389, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46721 p hg
    simpa only [d369389, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46947 (p : Pattern) (guard : d369390 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46946 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46722 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46948 (p : Pattern) (guard : d369391 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369390 p = 1 := by simpa only [d369391, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46947 p hg
    simpa only [d369391, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369391, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369391, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46949 (p : Pattern) (guard : d369392 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369391 p = 1 := by simpa only [d369392, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46948 p hg
    simpa only [d369392, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369392, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369392, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46950 (p : Pattern) (guard : d369393 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369393, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369393, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369392 p = 1 := by simpa only [d369393, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46949 p hg
    simpa only [d369393, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46951 (p : Pattern) (guard : d369394 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369393 p = 1 := by simpa only [d369394, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46950 p hg
    simpa only [d369394, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369394, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369394, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46952 (p : Pattern) (guard : d369395 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369394 p = 1 := by simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46951 p hg
    simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275508 p = 1 := by simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46730 p hg
    simpa only [d369395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46953 (p : Pattern) (guard : d369396 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369395 p = 1 := by simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46952 p hg
    simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275509 p = 1 := by simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46732 p hg
    simpa only [d369396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46954 (p : Pattern) (guard : d369397 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369396 p = 1 := by simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46953 p hg
    simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275510 p = 1 := by simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46733 p hg
    simpa only [d369397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46955 (p : Pattern) (guard : d369398 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369398, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d369398, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369397 p = 1 := by simpa only [d369398, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46954 p hg
    simpa only [d369398, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46956 (p : Pattern) (guard : d369399 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369399, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d369399, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369398 p = 1 := by simpa only [d369399, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46955 p hg
    simpa only [d369399, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46957 (p : Pattern) (guard : d369400 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369399 p = 1 := by simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46956 p hg
    simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275513 p = 1 := by simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46736 p hg
    simpa only [d369400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46958 (p : Pattern) (guard : d369401 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369400 p = 1 := by simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46957 p hg
    simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275514 p = 1 := by simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d369401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46959 (p : Pattern) (guard : d369402 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369401 p = 1 := by simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46958 p hg
    simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46960 (p : Pattern) (guard : d369403 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369402 p = 1 := by simpa only [d369403, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46959 p hg
    simpa only [d369403, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369403, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d369403, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46961 (p : Pattern) (guard : d369404 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369404, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d369404, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369403 p = 1 := by simpa only [d369404, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46960 p hg
    simpa only [d369404, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46962 (p : Pattern) (guard : d369405 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369404 p = 1 := by simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46961 p hg
    simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275518 p = 1 := by simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46743 p hg
    simpa only [d369405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46963 (p : Pattern) (guard : d369406 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369405 p = 1 := by simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46962 p hg
    simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46964 (p : Pattern) (guard : d369407 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369406 p = 1 := by simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46963 p hg
    simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46965 (p : Pattern) (guard : d369415 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369407 p = 1 := by simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46964 p hg
    simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46966 (p : Pattern) (guard : d369416 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369415 p = 1 := by simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46965 p hg
    simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275529 p = 1 := by simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46747 p hg
    simpa only [d369416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46967 (p : Pattern) (guard : d369417 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369416 p = 1 := by simpa only [d369417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46966 p hg
    simpa only [d369417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46968 (p : Pattern) (guard : d369418 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369417 p = 1 := by simpa only [d369418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46967 p hg
    simpa only [d369418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275531 p = 1 := by simpa only [d369418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46749 p hg
    simpa only [d369418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46969 (p : Pattern) (guard : d369426 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369418 p = 1 := by simpa only [d369426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46968 p hg
    simpa only [d369426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46970 (p : Pattern) (guard : d369427 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369426 p = 1 := by simpa only [d369427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46969 p hg
    simpa only [d369427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46971 (p : Pattern) (guard : d369428 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369428, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369428, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369427 p = 1 := by simpa only [d369428, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46970 p hg
    simpa only [d369428, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46972 (p : Pattern) (guard : d369429 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369428 p = 1 := by simpa only [d369429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46971 p hg
    simpa only [d369429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46973 (p : Pattern) (guard : d369430 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369429 p = 1 := by simpa only [d369430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46972 p hg
    simpa only [d369430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46974 (p : Pattern) (guard : d369431 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369430 p = 1 := by simpa only [d369431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46973 p hg
    simpa only [d369431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46975 (p : Pattern) (guard : d369432 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369431 p = 1 := by simpa only [d369432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46974 p hg
    simpa only [d369432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46976 (p : Pattern) (guard : d369433 p = 1) : d50676 p ≤ (1 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d369425 p = 1 := by simpa only [d369433, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46927 p hg
    simpa only [d369433, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369432 p = 1 := by simpa only [d369433, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46975 p hg
    simpa only [d369433, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46977 (p : Pattern) (guard : d44996 p = 1) : d47630 p ≤ (1 : Int) + d47630 p := by
  omega
theorem compare46978 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (1 : Int) + d49309 p := by
  have ha := bounds2 p
  have hb := bounds49309 p
  omega
theorem compare46979 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (1 : Int) + d47789 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46980 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (1 : Int) + d49310 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d49310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46978 p hg
    simpa only [d15, d47630, d49310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d49310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46979 p hg
    simpa only [d15, d47630, d49310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46981 (p : Pattern) (guard : d45587 p = 1) : d47630 p ≤ (1 : Int) + d49310 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46765 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46980 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46982 (p : Pattern) (guard : d45588 p = 1) : d47630 p ≤ (1 : Int) + d49311 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d45588, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46977 p hg
    simpa only [d45588, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d45588, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46981 p hg
    simpa only [d45588, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46983 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (1 : Int) + d49313 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46984 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (1 : Int) + d49312 p := by
  have ha := bounds2 p
  have hb := bounds49312 p
  omega
theorem compare46985 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (1 : Int) + d47633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46986 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (1 : Int) + d49313 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d49313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46984 p hg
    simpa only [d15, d47630, d49313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d49313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46985 p hg
    simpa only [d15, d47630, d49313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46987 (p : Pattern) (guard : d45587 p = 1) : d47630 p ≤ (1 : Int) + d49313 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46983 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46986 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46988 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (1 : Int) + d49314 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46989 (p : Pattern) (guard : d46472 p = 1) : d47630 p ≤ (1 : Int) + d49315 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46987 p hg
    simpa only [d46472, d49315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46988 p hg
    simpa only [d46472, d49315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46990 (p : Pattern) (guard : d369384 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 224 with
  | false =>
    have hg : d45588 p = 1 := by simpa only [d369384, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46982 p hg
    simpa only [d369384, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46472 p = 1 := by simpa only [d369384, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46989 p hg
    simpa only [d369384, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46991 (p : Pattern) (guard : d369385 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 223 with
  | false =>
    have hg : d369384 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46990 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d369385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46992 (p : Pattern) (guard : d369386 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369385 p = 1 := by simpa only [d369386, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46991 p hg
    simpa only [d369386, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369386, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46770 p hg
    simpa only [d369386, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46993 (p : Pattern) (guard : d369387 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369386 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46992 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46771 p hg
    simpa only [d369387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46994 (p : Pattern) (guard : d369388 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46993 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275501 p = 1 := by simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46772 p hg
    simpa only [d369388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46995 (p : Pattern) (guard : d369389 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369388 p = 1 := by simpa only [d369389, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46994 p hg
    simpa only [d369389, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369389, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46774 p hg
    simpa only [d369389, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46996 (p : Pattern) (guard : d369390 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46995 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46775 p hg
    simpa only [d369390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46997 (p : Pattern) (guard : d369434 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369434, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d369434, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369390 p = 1 := by simpa only [d369434, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46996 p hg
    simpa only [d369434, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46998 (p : Pattern) (guard : d369391 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369390 p = 1 := by simpa only [d369391, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46881 p hg
    simpa only [d369391, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369391, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369391, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46999 (p : Pattern) (guard : d369435 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369434 p = 1 := by simpa only [d369435, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46997 p hg
    simpa only [d369435, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369391 p = 1 := by simpa only [d369435, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46998 p hg
    simpa only [d369435, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
