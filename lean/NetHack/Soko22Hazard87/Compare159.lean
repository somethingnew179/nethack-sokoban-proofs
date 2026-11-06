import NetHack.Soko22Hazard87.Compare158
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39750 (p : Pattern) (guard : d324712 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324711 p = 1 := by simpa only [d324712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39749 p hg
    simpa only [d324712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d324712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39751 (p : Pattern) (guard : d324713 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324627 p = 1 := by simpa only [d324713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39657 p hg
    simpa only [d324713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324712 p = 1 := by simpa only [d324713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39750 p hg
    simpa only [d324713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39752 (p : Pattern) (guard : d324714 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324712 p = 1 := by simpa only [d324714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39750 p hg
    simpa only [d324714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d324714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39753 (p : Pattern) (guard : d324715 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324713 p = 1 := by simpa only [d324715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39751 p hg
    simpa only [d324715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324714 p = 1 := by simpa only [d324715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39752 p hg
    simpa only [d324715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39754 (p : Pattern) (guard : d324716 p = 1) : d50577 p ≤ (1 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324716, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d324716, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324715 p = 1 := by simpa only [d324716, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39753 p hg
    simpa only [d324716, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39755 (p : Pattern) (guard : d324717 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324717, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d324717, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324716 p = 1 := by simpa only [d324717, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39754 p hg
    simpa only [d324717, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39756 (p : Pattern) (guard : d324718 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324717 p = 1 := by simpa only [d324718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39755 p hg
    simpa only [d324718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39757 (p : Pattern) (guard : d324719 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324638 p = 1 := by simpa only [d324719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39674 p hg
    simpa only [d324719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324718 p = 1 := by simpa only [d324719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39756 p hg
    simpa only [d324719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39758 (p : Pattern) (guard : d324720 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324719 p = 1 := by simpa only [d324720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39757 p hg
    simpa only [d324720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39759 (p : Pattern) (guard : d324721 p = 1) : d50590 p ≤ (1 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324720 p = 1 := by simpa only [d324721, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39758 p hg
    simpa only [d324721, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324721, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d324721, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39760 (p : Pattern) (guard : d324722 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324722, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324722, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324721 p = 1 := by simpa only [d324722, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39759 p hg
    simpa only [d324722, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39761 (p : Pattern) (guard : d324723 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324722 p = 1 := by simpa only [d324723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39760 p hg
    simpa only [d324723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39762 (p : Pattern) (guard : d324724 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324723 p = 1 := by simpa only [d324724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39761 p hg
    simpa only [d324724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39763 (p : Pattern) (guard : d324725 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324724 p = 1 := by simpa only [d324725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39762 p hg
    simpa only [d324725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39764 (p : Pattern) (guard : d324726 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324725 p = 1 := by simpa only [d324726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39763 p hg
    simpa only [d324726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39765 (p : Pattern) (guard : d324727 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324726 p = 1 := by simpa only [d324727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39764 p hg
    simpa only [d324727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39766 (p : Pattern) (guard : d324728 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324727 p = 1 := by simpa only [d324728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39765 p hg
    simpa only [d324728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39767 (p : Pattern) (guard : d324729 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324706 p = 1 := by simpa only [d324729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39744 p hg
    simpa only [d324729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324728 p = 1 := by simpa only [d324729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39766 p hg
    simpa only [d324729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39768 (p : Pattern) (guard : d324730 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d324691 p = 1 := by simpa only [d324730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39729 p hg
    simpa only [d324730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324729 p = 1 := by simpa only [d324730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39767 p hg
    simpa only [d324730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39769 (p : Pattern) (guard : d324731 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d324682 p = 1 := by simpa only [d324731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39720 p hg
    simpa only [d324731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324730 p = 1 := by simpa only [d324731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39768 p hg
    simpa only [d324731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39770 (p : Pattern) (guard : d324732 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324731 p = 1 := by simpa only [d324732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39769 p hg
    simpa only [d324732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39771 (p : Pattern) (guard : d324733 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324675 p = 1 := by simpa only [d324733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39713 p hg
    simpa only [d324733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39772 (p : Pattern) (guard : d324734 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324677 p = 1 := by simpa only [d324734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39715 p hg
    simpa only [d324734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39773 (p : Pattern) (guard : d324735 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324733 p = 1 := by simpa only [d324735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39771 p hg
    simpa only [d324735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324734 p = 1 := by simpa only [d324735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39772 p hg
    simpa only [d324735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39774 (p : Pattern) (guard : d324736 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324735 p = 1 := by simpa only [d324736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39773 p hg
    simpa only [d324736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39775 (p : Pattern) (guard : d324737 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324736 p = 1 := by simpa only [d324737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39774 p hg
    simpa only [d324737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39776 (p : Pattern) (guard : d324738 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324737 p = 1 := by simpa only [d324738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39775 p hg
    simpa only [d324738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39777 (p : Pattern) (guard : d324739 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324684 p = 1 := by simpa only [d324739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39722 p hg
    simpa only [d324739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39778 (p : Pattern) (guard : d324740 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324687 p = 1 := by simpa only [d324740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39725 p hg
    simpa only [d324740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39779 (p : Pattern) (guard : d324741 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324739 p = 1 := by simpa only [d324741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39777 p hg
    simpa only [d324741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324740 p = 1 := by simpa only [d324741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39778 p hg
    simpa only [d324741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39780 (p : Pattern) (guard : d324742 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324741 p = 1 := by simpa only [d324742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39779 p hg
    simpa only [d324742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39781 (p : Pattern) (guard : d324743 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324742 p = 1 := by simpa only [d324743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39780 p hg
    simpa only [d324743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39782 (p : Pattern) (guard : d324744 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324703 p = 1 := by simpa only [d324744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39741 p hg
    simpa only [d324744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39783 (p : Pattern) (guard : d324745 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324744 p = 1 := by simpa only [d324745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39782 p hg
    simpa only [d324745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324664 p = 1 := by simpa only [d324745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39702 p hg
    simpa only [d324745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39784 (p : Pattern) (guard : d324746 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324745 p = 1 := by simpa only [d324746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39783 p hg
    simpa only [d324746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39785 (p : Pattern) (guard : d324747 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324725 p = 1 := by simpa only [d324747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39763 p hg
    simpa only [d324747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39786 (p : Pattern) (guard : d324748 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324747 p = 1 := by simpa only [d324748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39785 p hg
    simpa only [d324748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39787 (p : Pattern) (guard : d324749 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324748 p = 1 := by simpa only [d324749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39786 p hg
    simpa only [d324749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39788 (p : Pattern) (guard : d324750 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324746 p = 1 := by simpa only [d324750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39784 p hg
    simpa only [d324750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324749 p = 1 := by simpa only [d324750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39787 p hg
    simpa only [d324750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39789 (p : Pattern) (guard : d324751 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d324743 p = 1 := by simpa only [d324751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39781 p hg
    simpa only [d324751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324750 p = 1 := by simpa only [d324751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39788 p hg
    simpa only [d324751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39790 (p : Pattern) (guard : d324752 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d324738 p = 1 := by simpa only [d324752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39776 p hg
    simpa only [d324752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324751 p = 1 := by simpa only [d324752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39789 p hg
    simpa only [d324752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39791 (p : Pattern) (guard : d324753 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324731 p = 1 := by simpa only [d324753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39769 p hg
    simpa only [d324753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324752 p = 1 := by simpa only [d324753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39790 p hg
    simpa only [d324753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39792 (p : Pattern) (guard : d324754 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d324732 p = 1 := by simpa only [d324754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39770 p hg
    simpa only [d324754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324753 p = 1 := by simpa only [d324754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39791 p hg
    simpa only [d324754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39793 (p : Pattern) (guard : d324755 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324655 p = 1 := by simpa only [d324755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39693 p hg
    simpa only [d324755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39794 (p : Pattern) (guard : d324756 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324755 p = 1 := by simpa only [d324756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39793 p hg
    simpa only [d324756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39795 (p : Pattern) (guard : d324757 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324756 p = 1 := by simpa only [d324757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39794 p hg
    simpa only [d324757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39796 (p : Pattern) (guard : d324758 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324757 p = 1 := by simpa only [d324758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39795 p hg
    simpa only [d324758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39797 (p : Pattern) (guard : d324759 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324758 p = 1 := by simpa only [d324759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39796 p hg
    simpa only [d324759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39798 (p : Pattern) (guard : d324760 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324660 p = 1 := by simpa only [d324760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39698 p hg
    simpa only [d324760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324759 p = 1 := by simpa only [d324760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39797 p hg
    simpa only [d324760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39799 (p : Pattern) (guard : d324761 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324665 p = 1 := by simpa only [d324761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39703 p hg
    simpa only [d324761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39800 (p : Pattern) (guard : d324762 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324761 p = 1 := by simpa only [d324762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39799 p hg
    simpa only [d324762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39801 (p : Pattern) (guard : d324763 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324762 p = 1 := by simpa only [d324763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39800 p hg
    simpa only [d324763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39802 (p : Pattern) (guard : d324764 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324763 p = 1 := by simpa only [d324764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39801 p hg
    simpa only [d324764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39803 (p : Pattern) (guard : d324765 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324764 p = 1 := by simpa only [d324765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39802 p hg
    simpa only [d324765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39804 (p : Pattern) (guard : d324766 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324759 p = 1 := by simpa only [d324766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39797 p hg
    simpa only [d324766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324765 p = 1 := by simpa only [d324766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39803 p hg
    simpa only [d324766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39805 (p : Pattern) (guard : d324767 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d324760 p = 1 := by simpa only [d324767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39798 p hg
    simpa only [d324767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324766 p = 1 := by simpa only [d324767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39804 p hg
    simpa only [d324767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39806 (p : Pattern) (guard : d324768 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324754 p = 1 := by simpa only [d324768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39792 p hg
    simpa only [d324768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324767 p = 1 := by simpa only [d324768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39805 p hg
    simpa only [d324768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39807 (p : Pattern) (guard : d324769 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 51 with
  | false =>
    have hg : d324768 p = 1 := by simpa only [d324769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39806 p hg
    simpa only [d324769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39808 (p : Pattern) (guard : d324770 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 50 with
  | false =>
    have hg : d324674 p = 1 := by simpa only [d324770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39712 p hg
    simpa only [d324770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324769 p = 1 := by simpa only [d324770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39807 p hg
    simpa only [d324770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39809 (p : Pattern) (guard : d0 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39810 (p : Pattern) (guard : d0 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39811 (p : Pattern) (guard : d0 p = 1) : d50671 p ≤ (1 : Int) + d324514 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39812 (p : Pattern) (guard : d0 p = 1) : d50631 p ≤ (1 : Int) + d324493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39813 (p : Pattern) (guard : d0 p = 1) : d50653 p ≤ (1 : Int) + d324499 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39814 (p : Pattern) (guard : d0 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39815 (p : Pattern) (guard : d0 p = 1) : d50656 p ≤ (1 : Int) + d324502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39816 (p : Pattern) (guard : d0 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39817 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39818 (p : Pattern) (guard : d32155 p = 1) : d49565 p ≤ (1 : Int) + d49565 p := by
  omega
theorem compare39819 (p : Pattern) (guard : d324612 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324612, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d324612, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d324612, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39818 p hg
    simpa only [d324612, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39820 (p : Pattern) (guard : d0 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39821 (p : Pattern) (guard : d324613 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d324612 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39819 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39822 (p : Pattern) (guard : d324614 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d324613 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39821 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39823 (p : Pattern) (guard : d0 p = 1) : d49566 p ≤ (1 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39824 (p : Pattern) (guard : d324615 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 182 with
  | false =>
    have hg : d324614 p = 1 := by simpa only [d324615, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39822 p hg
    simpa only [d324615, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324615, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39823 p hg
    simpa only [d324615, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39825 (p : Pattern) (guard : d324616 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39816 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324615 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39824 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39826 (p : Pattern) (guard : d0 p = 1) : d50530 p ≤ (1 : Int) + d49328 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39827 (p : Pattern) (guard : d324617 p = 1) : d50657 p ≤ (1 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324616 p = 1 := by simpa only [d324617, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39825 p hg
    simpa only [d324617, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324617, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324617, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39828 (p : Pattern) (guard : d324618 p = 1) : d50658 p ≤ (1 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324617 p = 1 := by simpa only [d324618, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39827 p hg
    simpa only [d324618, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324618, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324618, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39829 (p : Pattern) (guard : d324619 p = 1) : d50659 p ≤ (1 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324619, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d324619, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324618 p = 1 := by simpa only [d324619, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39828 p hg
    simpa only [d324619, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39830 (p : Pattern) (guard : d0 p = 1) : d50662 p ≤ (1 : Int) + d324491 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39831 (p : Pattern) (guard : d324620 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324619 p = 1 := by simpa only [d324620, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39829 p hg
    simpa only [d324620, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324620, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d324620, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39832 (p : Pattern) (guard : d324621 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324620 p = 1 := by simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39831 p hg
    simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39833 (p : Pattern) (guard : d324692 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d324692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324621 p = 1 := by simpa only [d324692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39832 p hg
    simpa only [d324692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39834 (p : Pattern) (guard : d1115 p = 1) : d49565 p ≤ (1 : Int) + d49565 p := by
  omega
theorem compare39835 (p : Pattern) (guard : d221076 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221076, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d221076, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d221076, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39834 p hg
    simpa only [d221076, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39836 (p : Pattern) (guard : d221096 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221076 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39835 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39837 (p : Pattern) (guard : d19 p = 1) : d49565 p ≤ (1 : Int) + d49565 p := by
  omega
theorem compare39838 (p : Pattern) (guard : d221097 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221097, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d221097, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d221097, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39837 p hg
    simpa only [d221097, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39839 (p : Pattern) (guard : d221098 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221097 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39838 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39840 (p : Pattern) (guard : d221099 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221096 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39836 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221098 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39839 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39841 (p : Pattern) (guard : d221100 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221099 p = 1 := by simpa only [d221100, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39840 p hg
    simpa only [d221100, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221100, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39823 p hg
    simpa only [d221100, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39842 (p : Pattern) (guard : d324622 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39824 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221100 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39841 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39843 (p : Pattern) (guard : d324623 p = 1) : d50657 p ≤ (1 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324622 p = 1 := by simpa only [d324623, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39842 p hg
    simpa only [d324623, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324623, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324623, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39844 (p : Pattern) (guard : d324624 p = 1) : d50658 p ≤ (1 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324623 p = 1 := by simpa only [d324624, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39843 p hg
    simpa only [d324624, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324624, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324624, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39845 (p : Pattern) (guard : d324625 p = 1) : d50659 p ≤ (1 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324625, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d324625, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324624 p = 1 := by simpa only [d324625, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39844 p hg
    simpa only [d324625, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39846 (p : Pattern) (guard : d324626 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324625 p = 1 := by simpa only [d324626, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39845 p hg
    simpa only [d324626, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324626, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d324626, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39847 (p : Pattern) (guard : d324627 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324620 p = 1 := by simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39831 p hg
    simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324626 p = 1 := by simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39846 p hg
    simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39848 (p : Pattern) (guard : d324628 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324621 p = 1 := by simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39832 p hg
    simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324627 p = 1 := by simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39847 p hg
    simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39849 (p : Pattern) (guard : d324693 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324692 p = 1 := by simpa only [d324693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39833 p hg
    simpa only [d324693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324628 p = 1 := by simpa only [d324693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39848 p hg
    simpa only [d324693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39850 (p : Pattern) (guard : d324694 p = 1) : d50664 p ≤ (1 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324694, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d324694, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324693 p = 1 := by simpa only [d324694, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39849 p hg
    simpa only [d324694, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39851 (p : Pattern) (guard : d324695 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324695, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d324695, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324694 p = 1 := by simpa only [d324695, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39850 p hg
    simpa only [d324695, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39852 (p : Pattern) (guard : d324629 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324626 p = 1 := by simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39846 p hg
    simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39853 (p : Pattern) (guard : d324630 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324627 p = 1 := by simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39847 p hg
    simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324629 p = 1 := by simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39852 p hg
    simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39854 (p : Pattern) (guard : d324631 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324628 p = 1 := by simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39848 p hg
    simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324630 p = 1 := by simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39853 p hg
    simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39855 (p : Pattern) (guard : d324632 p = 1) : d50664 p ≤ (1 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324632, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d324632, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324631 p = 1 := by simpa only [d324632, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39854 p hg
    simpa only [d324632, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39856 (p : Pattern) (guard : d324633 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324633, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d324633, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324632 p = 1 := by simpa only [d324633, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39855 p hg
    simpa only [d324633, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39857 (p : Pattern) (guard : d324696 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324695 p = 1 := by simpa only [d324696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39851 p hg
    simpa only [d324696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324633 p = 1 := by simpa only [d324696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39856 p hg
    simpa only [d324696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39858 (p : Pattern) (guard : d221101 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221100 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39841 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39816 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39859 (p : Pattern) (guard : d221102 p = 1) : d50657 p ≤ (1 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221101 p = 1 := by simpa only [d221102, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39858 p hg
    simpa only [d221102, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221102, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d221102, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39860 (p : Pattern) (guard : d221103 p = 1) : d50658 p ≤ (1 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221102 p = 1 := by simpa only [d221103, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39859 p hg
    simpa only [d221103, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221103, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d221103, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39861 (p : Pattern) (guard : d221104 p = 1) : d50659 p ≤ (1 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221104, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d221104, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221103 p = 1 := by simpa only [d221104, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39860 p hg
    simpa only [d221104, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39862 (p : Pattern) (guard : d221105 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221104 p = 1 := by simpa only [d221105, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39861 p hg
    simpa only [d221105, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221105, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d221105, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39863 (p : Pattern) (guard : d221106 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221105 p = 1 := by simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39862 p hg
    simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39864 (p : Pattern) (guard : d324634 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324629 p = 1 := by simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39852 p hg
    simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221106 p = 1 := by simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39863 p hg
    simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39865 (p : Pattern) (guard : d324635 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324630 p = 1 := by simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39853 p hg
    simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324634 p = 1 := by simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39864 p hg
    simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39866 (p : Pattern) (guard : d324636 p = 1) : d50664 p ≤ (1 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324636, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d324636, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324635 p = 1 := by simpa only [d324636, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39865 p hg
    simpa only [d324636, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39867 (p : Pattern) (guard : d324637 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324637, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d324637, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324636 p = 1 := by simpa only [d324637, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39866 p hg
    simpa only [d324637, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39868 (p : Pattern) (guard : d324638 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324633 p = 1 := by simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39856 p hg
    simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324637 p = 1 := by simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39867 p hg
    simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39869 (p : Pattern) (guard : d324697 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324696 p = 1 := by simpa only [d324697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39857 p hg
    simpa only [d324697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324638 p = 1 := by simpa only [d324697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39868 p hg
    simpa only [d324697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39870 (p : Pattern) (guard : d0 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39871 (p : Pattern) (guard : d324698 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324697 p = 1 := by simpa only [d324698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39869 p hg
    simpa only [d324698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39872 (p : Pattern) (guard : d0 p = 1) : d50672 p ≤ (1 : Int) + d324515 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39873 (p : Pattern) (guard : d324699 p = 1) : d50673 p ≤ (1 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324698 p = 1 := by simpa only [d324699, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39871 p hg
    simpa only [d324699, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324699, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d324699, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39874 (p : Pattern) (guard : d324700 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324700, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d324700, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324699 p = 1 := by simpa only [d324700, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39873 p hg
    simpa only [d324700, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39875 (p : Pattern) (guard : d324639 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324637 p = 1 := by simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39867 p hg
    simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39876 (p : Pattern) (guard : d324640 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324638 p = 1 := by simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39868 p hg
    simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324639 p = 1 := by simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39875 p hg
    simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39877 (p : Pattern) (guard : d324641 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324640 p = 1 := by simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39876 p hg
    simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39878 (p : Pattern) (guard : d324642 p = 1) : d50673 p ≤ (1 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324641 p = 1 := by simpa only [d324642, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39877 p hg
    simpa only [d324642, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324642, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d324642, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39879 (p : Pattern) (guard : d324643 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324643, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d324643, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324642 p = 1 := by simpa only [d324643, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39878 p hg
    simpa only [d324643, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39880 (p : Pattern) (guard : d324701 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324700 p = 1 := by simpa only [d324701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39874 p hg
    simpa only [d324701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324643 p = 1 := by simpa only [d324701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39879 p hg
    simpa only [d324701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39881 (p : Pattern) (guard : d324702 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324701 p = 1 := by simpa only [d324702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39880 p hg
    simpa only [d324702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39882 (p : Pattern) (guard : d324703 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324702 p = 1 := by simpa only [d324703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39881 p hg
    simpa only [d324703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39883 (p : Pattern) (guard : d324744 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324703 p = 1 := by simpa only [d324744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39882 p hg
    simpa only [d324744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39884 (p : Pattern) (guard : d324644 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324639 p = 1 := by simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39875 p hg
    simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39885 (p : Pattern) (guard : d324645 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324644 p = 1 := by simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39884 p hg
    simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39886 (p : Pattern) (guard : d324646 p = 1) : d50673 p ≤ (1 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324645 p = 1 := by simpa only [d324646, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39885 p hg
    simpa only [d324646, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324646, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d324646, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39887 (p : Pattern) (guard : d324647 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324647, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d324647, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324646 p = 1 := by simpa only [d324647, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39886 p hg
    simpa only [d324647, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39888 (p : Pattern) (guard : d324648 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324643 p = 1 := by simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39879 p hg
    simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324647 p = 1 := by simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39887 p hg
    simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39889 (p : Pattern) (guard : d324649 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324648 p = 1 := by simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39888 p hg
    simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39890 (p : Pattern) (guard : d324650 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324649 p = 1 := by simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39889 p hg
    simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39891 (p : Pattern) (guard : d324664 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324650 p = 1 := by simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39890 p hg
    simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39892 (p : Pattern) (guard : d324745 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324744 p = 1 := by simpa only [d324745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39883 p hg
    simpa only [d324745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324664 p = 1 := by simpa only [d324745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39891 p hg
    simpa only [d324745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39893 (p : Pattern) (guard : d324746 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324745 p = 1 := by simpa only [d324746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39892 p hg
    simpa only [d324746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39894 (p : Pattern) (guard : d324707 p = 1) : d50642 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39824 p hg
    simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39816 p hg
    simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39895 (p : Pattern) (guard : d324708 p = 1) : d50657 p ≤ (1 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324707 p = 1 := by simpa only [d324708, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39894 p hg
    simpa only [d324708, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324708, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324708, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39896 (p : Pattern) (guard : d324709 p = 1) : d50658 p ≤ (1 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324708 p = 1 := by simpa only [d324709, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39895 p hg
    simpa only [d324709, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324709, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324709, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39897 (p : Pattern) (guard : d324710 p = 1) : d50659 p ≤ (1 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324710, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d324710, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324709 p = 1 := by simpa only [d324710, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39896 p hg
    simpa only [d324710, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39898 (p : Pattern) (guard : d324711 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324710 p = 1 := by simpa only [d324711, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39897 p hg
    simpa only [d324711, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324711, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d324711, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39899 (p : Pattern) (guard : d324712 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324711 p = 1 := by simpa only [d324712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39898 p hg
    simpa only [d324712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d324712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39900 (p : Pattern) (guard : d324713 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324627 p = 1 := by simpa only [d324713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39847 p hg
    simpa only [d324713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324712 p = 1 := by simpa only [d324713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39899 p hg
    simpa only [d324713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39901 (p : Pattern) (guard : d324714 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324712 p = 1 := by simpa only [d324714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39899 p hg
    simpa only [d324714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d324714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39902 (p : Pattern) (guard : d324715 p = 1) : d50663 p ≤ (1 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324713 p = 1 := by simpa only [d324715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39900 p hg
    simpa only [d324715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324714 p = 1 := by simpa only [d324715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39901 p hg
    simpa only [d324715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39903 (p : Pattern) (guard : d324716 p = 1) : d50664 p ≤ (1 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324716, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d324716, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324715 p = 1 := by simpa only [d324716, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39902 p hg
    simpa only [d324716, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39904 (p : Pattern) (guard : d324717 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324717, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d324717, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324716 p = 1 := by simpa only [d324717, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39903 p hg
    simpa only [d324717, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39905 (p : Pattern) (guard : d324718 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324717 p = 1 := by simpa only [d324718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39904 p hg
    simpa only [d324718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39906 (p : Pattern) (guard : d324719 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324638 p = 1 := by simpa only [d324719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39868 p hg
    simpa only [d324719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324718 p = 1 := by simpa only [d324719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39905 p hg
    simpa only [d324719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39907 (p : Pattern) (guard : d324720 p = 1) : d50665 p ≤ (1 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324719 p = 1 := by simpa only [d324720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39906 p hg
    simpa only [d324720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d324720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39908 (p : Pattern) (guard : d324721 p = 1) : d50673 p ≤ (1 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324720 p = 1 := by simpa only [d324721, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39907 p hg
    simpa only [d324721, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324721, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d324721, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39909 (p : Pattern) (guard : d324722 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324722, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d324722, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324721 p = 1 := by simpa only [d324722, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39908 p hg
    simpa only [d324722, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39910 (p : Pattern) (guard : d324723 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324722 p = 1 := by simpa only [d324723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39909 p hg
    simpa only [d324723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39911 (p : Pattern) (guard : d324724 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324723 p = 1 := by simpa only [d324724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39910 p hg
    simpa only [d324724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39912 (p : Pattern) (guard : d324725 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324724 p = 1 := by simpa only [d324725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39911 p hg
    simpa only [d324725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39913 (p : Pattern) (guard : d324747 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324725 p = 1 := by simpa only [d324747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39912 p hg
    simpa only [d324747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39914 (p : Pattern) (guard : d324748 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324747 p = 1 := by simpa only [d324748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39913 p hg
    simpa only [d324748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39915 (p : Pattern) (guard : d324749 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324748 p = 1 := by simpa only [d324749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39914 p hg
    simpa only [d324749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39916 (p : Pattern) (guard : d324750 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324746 p = 1 := by simpa only [d324750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39893 p hg
    simpa only [d324750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324749 p = 1 := by simpa only [d324750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39915 p hg
    simpa only [d324750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39917 (p : Pattern) (guard : d324771 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324750 p = 1 := by simpa only [d324771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39916 p hg
    simpa only [d324771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39918 (p : Pattern) (guard : d324772 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324771 p = 1 := by simpa only [d324772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39917 p hg
    simpa only [d324772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39919 (p : Pattern) (guard : d324773 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324773, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324773, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324772 p = 1 := by simpa only [d324773, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39918 p hg
    simpa only [d324773, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39920 (p : Pattern) (guard : d324774 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d324774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324773 p = 1 := by simpa only [d324774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39919 p hg
    simpa only [d324774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39921 (p : Pattern) (guard : d324652 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324647 p = 1 := by simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39887 p hg
    simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39922 (p : Pattern) (guard : d324653 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324652 p = 1 := by simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39921 p hg
    simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39923 (p : Pattern) (guard : d324654 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324653 p = 1 := by simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39922 p hg
    simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39924 (p : Pattern) (guard : d324665 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324654 p = 1 := by simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39923 p hg
    simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39925 (p : Pattern) (guard : d324761 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324665 p = 1 := by simpa only [d324761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39924 p hg
    simpa only [d324761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39926 (p : Pattern) (guard : d324762 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324761 p = 1 := by simpa only [d324762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39925 p hg
    simpa only [d324762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39927 (p : Pattern) (guard : d324763 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324762 p = 1 := by simpa only [d324763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39926 p hg
    simpa only [d324763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39928 (p : Pattern) (guard : d324764 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324763 p = 1 := by simpa only [d324764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39927 p hg
    simpa only [d324764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39929 (p : Pattern) (guard : d324765 p = 1) : d50674 p ≤ (1 : Int) + d324517 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d324765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324764 p = 1 := by simpa only [d324765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39928 p hg
    simpa only [d324765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39930 (p : Pattern) (guard : d324775 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324775, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324775, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324765 p = 1 := by simpa only [d324775, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39929 p hg
    simpa only [d324775, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39931 (p : Pattern) (guard : d324776 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d324776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324775 p = 1 := by simpa only [d324776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39930 p hg
    simpa only [d324776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39932 (p : Pattern) (guard : d324777 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324774 p = 1 := by simpa only [d324777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39920 p hg
    simpa only [d324777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324776 p = 1 := by simpa only [d324777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39931 p hg
    simpa only [d324777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39933 (p : Pattern) (guard : d324778 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 51 with
  | false =>
    have hg : d324777 p = 1 := by simpa only [d324778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39932 p hg
    simpa only [d324778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d324778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39934 (p : Pattern) (guard : d324779 p = 1) : d50675 p ≤ (1 : Int) + d324518 p := by
  cases selected : p 50 with
  | false =>
    have hg : d324778 p = 1 := by simpa only [d324779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39933 p hg
    simpa only [d324779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d324779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39935 (p : Pattern) (guard : d324780 p = 1) : d50676 p ≤ (1 : Int) + d324519 p := by
  cases selected : p 49 with
  | false =>
    have hg : d324770 p = 1 := by simpa only [d324780, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39808 p hg
    simpa only [d324780, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324779 p = 1 := by simpa only [d324780, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39934 p hg
    simpa only [d324780, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39936 (p : Pattern) (guard : d0 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39937 (p : Pattern) (guard : d0 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39938 (p : Pattern) (guard : d0 p = 1) : d50712 p ≤ (1 : Int) + d324532 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39939 (p : Pattern) (guard : d0 p = 1) : d50724 p ≤ (1 : Int) + d324539 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39940 (p : Pattern) (guard : d0 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39941 (p : Pattern) (guard : d0 p = 1) : d50725 p ≤ (1 : Int) + d49670 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39942 (p : Pattern) (guard : d0 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39943 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (1 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39944 (p : Pattern) (guard : d32155 p = 1) : d49316 p ≤ (1 : Int) + d49316 p := by
  omega
theorem compare39945 (p : Pattern) (guard : d324612 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324612, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d324612, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d324612, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39944 p hg
    simpa only [d324612, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39946 (p : Pattern) (guard : d0 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39947 (p : Pattern) (guard : d324613 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d324612 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39948 (p : Pattern) (guard : d324614 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d324613 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39947 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39949 (p : Pattern) (guard : d0 p = 1) : d49317 p ≤ (1 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39950 (p : Pattern) (guard : d324615 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 182 with
  | false =>
    have hg : d324614 p = 1 := by simpa only [d324615, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39948 p hg
    simpa only [d324615, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324615, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39949 p hg
    simpa only [d324615, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39951 (p : Pattern) (guard : d324616 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39942 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324615 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39950 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39952 (p : Pattern) (guard : d324781 p = 1) : d50726 p ≤ (1 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324781, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d324781, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324616 p = 1 := by simpa only [d324781, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39951 p hg
    simpa only [d324781, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39953 (p : Pattern) (guard : d324617 p = 1) : d50727 p ≤ (1 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324616 p = 1 := by simpa only [d324617, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39635 p hg
    simpa only [d324617, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324617, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324617, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39954 (p : Pattern) (guard : d324782 p = 1) : d50728 p ≤ (1 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324781 p = 1 := by simpa only [d324782, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39952 p hg
    simpa only [d324782, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324617 p = 1 := by simpa only [d324782, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39953 p hg
    simpa only [d324782, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39955 (p : Pattern) (guard : d0 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39956 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39957 (p : Pattern) (guard : d32155 p = 1) : d49323 p ≤ (1 : Int) + d49323 p := by
  omega
theorem compare39958 (p : Pattern) (guard : d324612 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324612, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d324612, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d324612, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39957 p hg
    simpa only [d324612, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39959 (p : Pattern) (guard : d0 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39960 (p : Pattern) (guard : d324613 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d324612 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39958 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39961 (p : Pattern) (guard : d324614 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d324613 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39960 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39962 (p : Pattern) (guard : d0 p = 1) : d49324 p ≤ (1 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39963 (p : Pattern) (guard : d324615 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d324614 p = 1 := by simpa only [d324615, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39961 p hg
    simpa only [d324615, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324615, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39962 p hg
    simpa only [d324615, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39964 (p : Pattern) (guard : d324616 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39955 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324615 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39963 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39965 (p : Pattern) (guard : d324617 p = 1) : d50573 p ≤ (1 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324616 p = 1 := by simpa only [d324617, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39964 p hg
    simpa only [d324617, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324617, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324617, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39966 (p : Pattern) (guard : d324618 p = 1) : d50574 p ≤ (1 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324617 p = 1 := by simpa only [d324618, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39965 p hg
    simpa only [d324618, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324618, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324618, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39967 (p : Pattern) (guard : d324783 p = 1) : d50729 p ≤ (1 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d324782 p = 1 := by simpa only [d324783, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39954 p hg
    simpa only [d324783, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324618 p = 1 := by simpa only [d324783, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39966 p hg
    simpa only [d324783, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39968 (p : Pattern) (guard : d0 p = 1) : d50732 p ≤ (1 : Int) + d324546 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39969 (p : Pattern) (guard : d324784 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324783 p = 1 := by simpa only [d324784, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39967 p hg
    simpa only [d324784, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324784, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d324784, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39970 (p : Pattern) (guard : d324785 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d324785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324784 p = 1 := by simpa only [d324785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39969 p hg
    simpa only [d324785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39971 (p : Pattern) (guard : d324786 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d324786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324785 p = 1 := by simpa only [d324786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39970 p hg
    simpa only [d324786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39972 (p : Pattern) (guard : d1115 p = 1) : d49316 p ≤ (1 : Int) + d49316 p := by
  omega
theorem compare39973 (p : Pattern) (guard : d221076 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221076, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d221076, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d221076, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39972 p hg
    simpa only [d221076, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39974 (p : Pattern) (guard : d221096 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221076 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39973 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39975 (p : Pattern) (guard : d19 p = 1) : d49316 p ≤ (1 : Int) + d49316 p := by
  omega
theorem compare39976 (p : Pattern) (guard : d221097 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221097, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d221097, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d221097, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39975 p hg
    simpa only [d221097, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39977 (p : Pattern) (guard : d221098 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221097 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39976 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39978 (p : Pattern) (guard : d221099 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221096 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39974 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221098 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39977 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39979 (p : Pattern) (guard : d221100 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221099 p = 1 := by simpa only [d221100, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39978 p hg
    simpa only [d221100, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221100, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39949 p hg
    simpa only [d221100, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39980 (p : Pattern) (guard : d324622 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39950 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221100 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39979 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39981 (p : Pattern) (guard : d324787 p = 1) : d50726 p ≤ (1 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324787, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d324787, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324622 p = 1 := by simpa only [d324787, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39980 p hg
    simpa only [d324787, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39982 (p : Pattern) (guard : d324623 p = 1) : d50727 p ≤ (1 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324622 p = 1 := by simpa only [d324623, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39652 p hg
    simpa only [d324623, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324623, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324623, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39983 (p : Pattern) (guard : d324788 p = 1) : d50728 p ≤ (1 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324787 p = 1 := by simpa only [d324788, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39981 p hg
    simpa only [d324788, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324623 p = 1 := by simpa only [d324788, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39982 p hg
    simpa only [d324788, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39984 (p : Pattern) (guard : d1115 p = 1) : d49323 p ≤ (1 : Int) + d49323 p := by
  omega
theorem compare39985 (p : Pattern) (guard : d221076 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221076, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d221076, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d221076, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39984 p hg
    simpa only [d221076, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39986 (p : Pattern) (guard : d221096 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221076 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39985 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39987 (p : Pattern) (guard : d19 p = 1) : d49323 p ≤ (1 : Int) + d49323 p := by
  omega
theorem compare39988 (p : Pattern) (guard : d221097 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221097, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d221097, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d221097, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39987 p hg
    simpa only [d221097, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39989 (p : Pattern) (guard : d221098 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221097 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39990 (p : Pattern) (guard : d221099 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221096 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39986 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221098 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39989 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39991 (p : Pattern) (guard : d221100 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221099 p = 1 := by simpa only [d221100, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39990 p hg
    simpa only [d221100, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221100, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39962 p hg
    simpa only [d221100, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39992 (p : Pattern) (guard : d324622 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39963 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221100 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39991 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39993 (p : Pattern) (guard : d324623 p = 1) : d50573 p ≤ (1 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324622 p = 1 := by simpa only [d324623, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39992 p hg
    simpa only [d324623, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324623, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324623, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39994 (p : Pattern) (guard : d324624 p = 1) : d50574 p ≤ (1 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324623 p = 1 := by simpa only [d324624, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39993 p hg
    simpa only [d324624, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324624, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324624, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39995 (p : Pattern) (guard : d324789 p = 1) : d50729 p ≤ (1 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d324788 p = 1 := by simpa only [d324789, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39983 p hg
    simpa only [d324789, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324624 p = 1 := by simpa only [d324789, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39994 p hg
    simpa only [d324789, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39996 (p : Pattern) (guard : d324790 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324789 p = 1 := by simpa only [d324790, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39995 p hg
    simpa only [d324790, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324790, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d324790, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39997 (p : Pattern) (guard : d324791 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324784 p = 1 := by simpa only [d324791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39969 p hg
    simpa only [d324791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324790 p = 1 := by simpa only [d324791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39996 p hg
    simpa only [d324791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39998 (p : Pattern) (guard : d324792 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324785 p = 1 := by simpa only [d324792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39970 p hg
    simpa only [d324792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324791 p = 1 := by simpa only [d324792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39997 p hg
    simpa only [d324792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39999 (p : Pattern) (guard : d324793 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324786 p = 1 := by simpa only [d324793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39971 p hg
    simpa only [d324793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324792 p = 1 := by simpa only [d324793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d324793, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
