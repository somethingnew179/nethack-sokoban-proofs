import NetHack.Soko22Hazard87.Compare078
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19750 (p : Pattern) (guard : d16791 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19743 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19749 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19751 (p : Pattern) (guard : d16864 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16863 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19732 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16791 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19750 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19752 (p : Pattern) (guard : d16865 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16865, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16865, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16864 p = 1 := by simpa only [d16865, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19751 p hg
    simpa only [d16865, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19753 (p : Pattern) (guard : d16866 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16866, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16866, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16865 p = 1 := by simpa only [d16866, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19752 p hg
    simpa only [d16866, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19754 (p : Pattern) (guard : d10098 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19755 (p : Pattern) (guard : d10099 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10098 p = 1 := by simpa only [d10099, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19754 p hg
    simpa only [d10099, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10099, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10099, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19756 (p : Pattern) (guard : d10101 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10099 p = 1 := by simpa only [d10101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19755 p hg
    simpa only [d10101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19757 (p : Pattern) (guard : d13348 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13348, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d13348, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10101 p = 1 := by simpa only [d13348, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19756 p hg
    simpa only [d13348, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19758 (p : Pattern) (guard : d13349 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13348 p = 1 := by simpa only [d13349, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19757 p hg
    simpa only [d13349, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13349, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d13349, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19759 (p : Pattern) (guard : d16867 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13349 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19758 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19748 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19760 (p : Pattern) (guard : d15158 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19748 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19761 (p : Pattern) (guard : d16868 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16867 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19759 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19760 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19762 (p : Pattern) (guard : d16869 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19750 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16868 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19761 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19763 (p : Pattern) (guard : d16870 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16870, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16870, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16869 p = 1 := by simpa only [d16870, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19762 p hg
    simpa only [d16870, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19764 (p : Pattern) (guard : d16871 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16871, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16871, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16870 p = 1 := by simpa only [d16871, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19763 p hg
    simpa only [d16871, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19765 (p : Pattern) (guard : d16872 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16866 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19753 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16871 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19764 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19766 (p : Pattern) (guard : d1569 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19767 (p : Pattern) (guard : d1570 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19766 p hg
    simpa only [d1570, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d1570, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19768 (p : Pattern) (guard : d1571 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19767 p hg
    simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19769 (p : Pattern) (guard : d1572 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19768 p hg
    simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19770 (p : Pattern) (guard : d1573 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19769 p hg
    simpa only [d1573, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d1573, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19771 (p : Pattern) (guard : d10114 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19772 (p : Pattern) (guard : d10115 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10114 p = 1 := by simpa only [d10115, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19771 p hg
    simpa only [d10115, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10115, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10115, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19773 (p : Pattern) (guard : d10117 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10115 p = 1 := by simpa only [d10117, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19772 p hg
    simpa only [d10117, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10117, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10117, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19774 (p : Pattern) (guard : d16792 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16792, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d16792, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10117 p = 1 := by simpa only [d16792, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19773 p hg
    simpa only [d16792, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19775 (p : Pattern) (guard : d16793 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19774 p hg
    simpa only [d16793, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d16793, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19776 (p : Pattern) (guard : d16794 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19770 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19775 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19777 (p : Pattern) (guard : d16795 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19776 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19760 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19778 (p : Pattern) (guard : d16796 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19750 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19777 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19779 (p : Pattern) (guard : d16797 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16797, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19778 p hg
    simpa only [d16797, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19780 (p : Pattern) (guard : d16798 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16798, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19779 p hg
    simpa only [d16798, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19781 (p : Pattern) (guard : d5133 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19782 (p : Pattern) (guard : d5134 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19781 p hg
    simpa only [d5134, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d5134, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19783 (p : Pattern) (guard : d5135 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19782 p hg
    simpa only [d5135, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d5135, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19784 (p : Pattern) (guard : d5136 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d5136, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19783 p hg
    simpa only [d5136, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19785 (p : Pattern) (guard : d5137 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19784 p hg
    simpa only [d5137, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d5137, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19786 (p : Pattern) (guard : d5138 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19785 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19787 (p : Pattern) (guard : d10134 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19788 (p : Pattern) (guard : d10135 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10134 p = 1 := by simpa only [d10135, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19787 p hg
    simpa only [d10135, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10135, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10135, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19789 (p : Pattern) (guard : d10137 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10135 p = 1 := by simpa only [d10137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19788 p hg
    simpa only [d10137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19790 (p : Pattern) (guard : d15163 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15163, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d15163, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10137 p = 1 := by simpa only [d15163, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19789 p hg
    simpa only [d15163, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19791 (p : Pattern) (guard : d15164 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19790 p hg
    simpa only [d15164, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d15164, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19792 (p : Pattern) (guard : d15165 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19791 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19793 (p : Pattern) (guard : d15166 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19786 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19792 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19794 (p : Pattern) (guard : d16799 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19777 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19793 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19795 (p : Pattern) (guard : d16800 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16800, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19794 p hg
    simpa only [d16800, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19796 (p : Pattern) (guard : d16801 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16801, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19795 p hg
    simpa only [d16801, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19797 (p : Pattern) (guard : d16802 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19780 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19796 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19798 (p : Pattern) (guard : d16873 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16872 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19765 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16802 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19797 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19799 (p : Pattern) (guard : d16874 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16873 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19798 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19800 (p : Pattern) (guard : d16875 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16874 p = 1 := by simpa only [d16875, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19799 p hg
    simpa only [d16875, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16875, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16875, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19801 (p : Pattern) (guard : d16876 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16876, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16876, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16875 p = 1 := by simpa only [d16876, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19800 p hg
    simpa only [d16876, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19802 (p : Pattern) (guard : d16877 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16801 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19796 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19803 (p : Pattern) (guard : d16878 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19797 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16877 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19802 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19804 (p : Pattern) (guard : d16879 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16878 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19803 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19805 (p : Pattern) (guard : d16880 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16879 p = 1 := by simpa only [d16880, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19804 p hg
    simpa only [d16880, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16880, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16880, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19806 (p : Pattern) (guard : d16881 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16881, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16881, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16880 p = 1 := by simpa only [d16881, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19805 p hg
    simpa only [d16881, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19807 (p : Pattern) (guard : d16882 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16876 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19801 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16881 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19806 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19808 (p : Pattern) (guard : d16883 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16882 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19807 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19809 (p : Pattern) (guard : d16884 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16883 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19808 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19810 (p : Pattern) (guard : d16958 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16884 p = 1 := by simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19809 p hg
    simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19811 (p : Pattern) (guard : d1581 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19812 (p : Pattern) (guard : d1582 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19811 p hg
    simpa only [d1582, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d1582, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19813 (p : Pattern) (guard : d1583 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19812 p hg
    simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19814 (p : Pattern) (guard : d1584 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19813 p hg
    simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19815 (p : Pattern) (guard : d1585 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19814 p hg
    simpa only [d1585, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d1585, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19816 (p : Pattern) (guard : d1588 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19815 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19817 (p : Pattern) (guard : d15171 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19816 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19792 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19818 (p : Pattern) (guard : d16803 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19777 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19817 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19819 (p : Pattern) (guard : d16804 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16804, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19818 p hg
    simpa only [d16804, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19820 (p : Pattern) (guard : d16805 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16805, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19819 p hg
    simpa only [d16805, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19821 (p : Pattern) (guard : d16806 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19820 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19822 (p : Pattern) (guard : d16811 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19821 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19823 (p : Pattern) (guard : d16812 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19822 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19824 (p : Pattern) (guard : d16813 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19823 p hg
    simpa only [d16813, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16813, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19825 (p : Pattern) (guard : d16814 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19824 p hg
    simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19826 (p : Pattern) (guard : d16886 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16881 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19806 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19825 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19827 (p : Pattern) (guard : d16887 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16886 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19828 (p : Pattern) (guard : d16888 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16887 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19827 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19829 (p : Pattern) (guard : d16959 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16888 p = 1 := by simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19830 (p : Pattern) (guard : d16960 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16958 p = 1 := by simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19810 p hg
    simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16959 p = 1 := by simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19831 (p : Pattern) (guard : d128358 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16960 p = 1 := by simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19830 p hg
    simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19832 (p : Pattern) (guard : d13287 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19816 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19833 (p : Pattern) (guard : d16929 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19777 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13287 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19832 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19834 (p : Pattern) (guard : d16930 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16930, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16930, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16929 p = 1 := by simpa only [d16930, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19833 p hg
    simpa only [d16930, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19835 (p : Pattern) (guard : d16931 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16931, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16931, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16930 p = 1 := by simpa only [d16931, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d16931, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19836 (p : Pattern) (guard : d16932 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16931 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19835 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19837 (p : Pattern) (guard : d16933 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19797 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16932 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19836 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19838 (p : Pattern) (guard : d16934 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16933 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19837 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19839 (p : Pattern) (guard : d16935 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16934 p = 1 := by simpa only [d16935, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19838 p hg
    simpa only [d16935, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16935, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16935, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19840 (p : Pattern) (guard : d16936 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16936, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16936, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16935 p = 1 := by simpa only [d16936, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19839 p hg
    simpa only [d16936, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19841 (p : Pattern) (guard : d16937 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16936 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19840 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19842 (p : Pattern) (guard : d16938 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16937 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19841 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19843 (p : Pattern) (guard : d16939 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16938 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19842 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19844 (p : Pattern) (guard : d16965 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16939 p = 1 := by simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19843 p hg
    simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19845 (p : Pattern) (guard : d16966 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16965 p = 1 := by simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19844 p hg
    simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19846 (p : Pattern) (guard : d16967 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16966 p = 1 := by simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19845 p hg
    simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19847 (p : Pattern) (guard : d128359 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128358 p = 1 := by simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19831 p hg
    simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16967 p = 1 := by simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19848 (p : Pattern) (guard : d128367 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128359 p = 1 := by simpa only [d128367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19847 p hg
    simpa only [d128367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19849 (p : Pattern) (guard : d128368 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128367 p = 1 := by simpa only [d128368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19848 p hg
    simpa only [d128368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19850 (p : Pattern) (guard : d128369 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128369, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128369, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128368 p = 1 := by simpa only [d128369, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19849 p hg
    simpa only [d128369, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19851 (p : Pattern) (guard : d128370 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128369 p = 1 := by simpa only [d128370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19850 p hg
    simpa only [d128370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19852 (p : Pattern) (guard : d16819 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19825 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19853 (p : Pattern) (guard : d16820 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19852 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19854 (p : Pattern) (guard : d16821 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19853 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19855 (p : Pattern) (guard : d16832 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16821 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19854 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19856 (p : Pattern) (guard : d16984 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16832 p = 1 := by simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19855 p hg
    simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19857 (p : Pattern) (guard : d16985 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16984 p = 1 := by simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19856 p hg
    simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19858 (p : Pattern) (guard : d16986 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16985 p = 1 := by simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19857 p hg
    simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19859 (p : Pattern) (guard : d16987 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16986 p = 1 := by simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19858 p hg
    simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19860 (p : Pattern) (guard : d16988 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16987 p = 1 := by simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19861 (p : Pattern) (guard : d16998 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16998, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16998, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16988 p = 1 := by simpa only [d16998, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d16998, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19862 (p : Pattern) (guard : d16999 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d16999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16998 p = 1 := by simpa only [d16999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19861 p hg
    simpa only [d16999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19863 (p : Pattern) (guard : d128371 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128370 p = 1 := by simpa only [d128371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19851 p hg
    simpa only [d128371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16999 p = 1 := by simpa only [d128371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d128371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19864 (p : Pattern) (guard : d128372 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128371 p = 1 := by simpa only [d128372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19863 p hg
    simpa only [d128372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19865 (p : Pattern) (guard : d128373 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128372 p = 1 := by simpa only [d128373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19864 p hg
    simpa only [d128373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19866 (p : Pattern) (guard : d128374 p = 1) : d48359 p ≤ (1 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128366 p = 1 := by simpa only [d128374, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19709 p hg
    simpa only [d128374, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128373 p = 1 := by simpa only [d128374, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d128374, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19867 (p : Pattern) (guard : d175484 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128374 p = 1 := by simpa only [d175484, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19866 p hg
    simpa only [d175484, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175484, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d175484, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19868 (p : Pattern) (guard : d175485 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175484 p = 1 := by simpa only [d175485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19867 p hg
    simpa only [d175485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19869 (p : Pattern) (guard : d175486 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175485 p = 1 := by simpa only [d175486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19868 p hg
    simpa only [d175486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19870 (p : Pattern) (guard : d175487 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175486 p = 1 := by simpa only [d175487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19869 p hg
    simpa only [d175487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19871 (p : Pattern) (guard : d175488 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175487 p = 1 := by simpa only [d175488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19870 p hg
    simpa only [d175488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19872 (p : Pattern) (guard : d175489 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175488 p = 1 := by simpa only [d175489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19871 p hg
    simpa only [d175489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19873 (p : Pattern) (guard : d175490 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175489 p = 1 := by simpa only [d175490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19872 p hg
    simpa only [d175490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19874 (p : Pattern) (guard : d175491 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175490 p = 1 := by simpa only [d175491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19873 p hg
    simpa only [d175491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19875 (p : Pattern) (guard : d175492 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175491 p = 1 := by simpa only [d175492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19874 p hg
    simpa only [d175492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19876 (p : Pattern) (guard : d175493 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175492 p = 1 := by simpa only [d175493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19875 p hg
    simpa only [d175493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19877 (p : Pattern) (guard : d175494 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d175483 p = 1 := by simpa only [d175494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19391 p hg
    simpa only [d175494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175493 p = 1 := by simpa only [d175494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19876 p hg
    simpa only [d175494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19878 (p : Pattern) (guard : d2034 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19879 (p : Pattern) (guard : d2035 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19878 p hg
    simpa only [d2035, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d2035, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19880 (p : Pattern) (guard : d2036 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19879 p hg
    simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19881 (p : Pattern) (guard : d2037 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d2037, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19880 p hg
    simpa only [d2037, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19882 (p : Pattern) (guard : d2038 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19881 p hg
    simpa only [d2038, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d2038, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19883 (p : Pattern) (guard : d10363 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19884 (p : Pattern) (guard : d10364 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10363 p = 1 := by simpa only [d10364, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19883 p hg
    simpa only [d10364, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10364, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10364, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19885 (p : Pattern) (guard : d10366 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10364 p = 1 := by simpa only [d10366, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19884 p hg
    simpa only [d10366, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10366, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10366, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19886 (p : Pattern) (guard : d17153 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17153, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d17153, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10366 p = 1 := by simpa only [d17153, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19885 p hg
    simpa only [d17153, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19887 (p : Pattern) (guard : d17154 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19886 p hg
    simpa only [d17154, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d17154, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19888 (p : Pattern) (guard : d17155 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19882 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19887 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19889 (p : Pattern) (guard : d10352 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19890 (p : Pattern) (guard : d10353 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10352 p = 1 := by simpa only [d10353, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d10353, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10353, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10353, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19891 (p : Pattern) (guard : d10355 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10353 p = 1 := by simpa only [d10355, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d10355, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10355, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10355, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19892 (p : Pattern) (guard : d13675 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13675, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d13675, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10355 p = 1 := by simpa only [d13675, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19891 p hg
    simpa only [d13675, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19893 (p : Pattern) (guard : d13676 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19892 p hg
    simpa only [d13676, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d13676, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19894 (p : Pattern) (guard : d10370 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19895 (p : Pattern) (guard : d10371 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10370 p = 1 := by simpa only [d10371, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19894 p hg
    simpa only [d10371, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10371, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10371, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19896 (p : Pattern) (guard : d10373 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10371 p = 1 := by simpa only [d10373, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19895 p hg
    simpa only [d10373, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10373, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10373, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19897 (p : Pattern) (guard : d15548 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15548, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d15548, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10373 p = 1 := by simpa only [d15548, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19896 p hg
    simpa only [d15548, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19898 (p : Pattern) (guard : d15549 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19897 p hg
    simpa only [d15549, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d15549, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19899 (p : Pattern) (guard : d17156 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19898 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19900 (p : Pattern) (guard : d17157 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19888 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19899 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19901 (p : Pattern) (guard : d2052 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19902 (p : Pattern) (guard : d2053 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19901 p hg
    simpa only [d2053, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d2053, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19903 (p : Pattern) (guard : d2054 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19902 p hg
    simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19904 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d2055, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19903 p hg
    simpa only [d2055, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19905 (p : Pattern) (guard : d2056 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19904 p hg
    simpa only [d2056, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d2056, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19906 (p : Pattern) (guard : d10390 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19907 (p : Pattern) (guard : d10391 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10390 p = 1 := by simpa only [d10391, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19906 p hg
    simpa only [d10391, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10391, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10391, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19908 (p : Pattern) (guard : d10393 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10391 p = 1 := by simpa only [d10393, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19907 p hg
    simpa only [d10393, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10393, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10393, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19909 (p : Pattern) (guard : d17158 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17158, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d17158, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10393 p = 1 := by simpa only [d17158, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19908 p hg
    simpa only [d17158, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19910 (p : Pattern) (guard : d17159 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19909 p hg
    simpa only [d17159, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d17159, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19911 (p : Pattern) (guard : d17160 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19905 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19910 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19912 (p : Pattern) (guard : d15550 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19898 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19913 (p : Pattern) (guard : d17161 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19911 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19912 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19914 (p : Pattern) (guard : d17162 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19900 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19913 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19915 (p : Pattern) (guard : d17163 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d17163, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19914 p hg
    simpa only [d17163, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19916 (p : Pattern) (guard : d17164 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d17164, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d17164, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19917 (p : Pattern) (guard : d5246 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19918 (p : Pattern) (guard : d5247 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19917 p hg
    simpa only [d5247, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d5247, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19919 (p : Pattern) (guard : d5248 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19920 (p : Pattern) (guard : d5249 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d5249, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19919 p hg
    simpa only [d5249, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19921 (p : Pattern) (guard : d5250 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19920 p hg
    simpa only [d5250, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d5250, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19922 (p : Pattern) (guard : d5251 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19921 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19923 (p : Pattern) (guard : d10411 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19924 (p : Pattern) (guard : d10412 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10411 p = 1 := by simpa only [d10412, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19923 p hg
    simpa only [d10412, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10412, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10412, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19925 (p : Pattern) (guard : d10414 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10412 p = 1 := by simpa only [d10414, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19924 p hg
    simpa only [d10414, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10414, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10414, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19926 (p : Pattern) (guard : d15555 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15555, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d15555, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10414 p = 1 := by simpa only [d15555, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19925 p hg
    simpa only [d15555, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19927 (p : Pattern) (guard : d15556 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19926 p hg
    simpa only [d15556, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d15556, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19928 (p : Pattern) (guard : d15557 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19927 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19929 (p : Pattern) (guard : d15558 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19922 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19930 (p : Pattern) (guard : d17165 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19913 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19929 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19931 (p : Pattern) (guard : d17166 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d17166, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19930 p hg
    simpa only [d17166, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19932 (p : Pattern) (guard : d17167 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d17167, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19931 p hg
    simpa only [d17167, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19933 (p : Pattern) (guard : d17168 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19932 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19934 (p : Pattern) (guard : d2064 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19935 (p : Pattern) (guard : d2065 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19934 p hg
    simpa only [d2065, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d2065, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19936 (p : Pattern) (guard : d2066 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19935 p hg
    simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19937 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d2067, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19936 p hg
    simpa only [d2067, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19938 (p : Pattern) (guard : d2068 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d2068, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d2068, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19939 (p : Pattern) (guard : d2071 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19938 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19940 (p : Pattern) (guard : d15563 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19941 (p : Pattern) (guard : d17169 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19913 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19940 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19942 (p : Pattern) (guard : d17170 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d17170, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19941 p hg
    simpa only [d17170, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19943 (p : Pattern) (guard : d17171 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d17171, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19942 p hg
    simpa only [d17171, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19944 (p : Pattern) (guard : d17172 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19943 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19945 (p : Pattern) (guard : d17173 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19933 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19944 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19946 (p : Pattern) (guard : d17174 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19945 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19947 (p : Pattern) (guard : d17175 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19946 p hg
    simpa only [d17175, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17175, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19948 (p : Pattern) (guard : d17176 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d17176, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19947 p hg
    simpa only [d17176, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19949 (p : Pattern) (guard : d17177 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19944 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19950 (p : Pattern) (guard : d17178 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19949 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19951 (p : Pattern) (guard : d17179 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19950 p hg
    simpa only [d17179, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17179, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19952 (p : Pattern) (guard : d17180 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d17180, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19951 p hg
    simpa only [d17180, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19953 (p : Pattern) (guard : d17181 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19948 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19952 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19954 (p : Pattern) (guard : d17182 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19953 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19955 (p : Pattern) (guard : d17183 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19954 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19956 (p : Pattern) (guard : d17184 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17183 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19955 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19957 (p : Pattern) (guard : d17185 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19952 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19958 (p : Pattern) (guard : d17186 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19957 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19959 (p : Pattern) (guard : d17187 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19958 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19960 (p : Pattern) (guard : d17188 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17187 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19959 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19961 (p : Pattern) (guard : d17189 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17184 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19956 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19960 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19962 (p : Pattern) (guard : d17190 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17189 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19961 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19963 (p : Pattern) (guard : d17191 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17190 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19962 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19964 (p : Pattern) (guard : d17192 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17191 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19963 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19965 (p : Pattern) (guard : d17193 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17192 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19964 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19966 (p : Pattern) (guard : d17194 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17193 p = 1 := by simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19965 p hg
    simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19967 (p : Pattern) (guard : d17195 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d17195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17194 p = 1 := by simpa only [d17195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19966 p hg
    simpa only [d17195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19968 (p : Pattern) (guard : d17196 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d17195 p = 1 := by simpa only [d17196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19967 p hg
    simpa only [d17196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d17196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19969 (p : Pattern) (guard : d17164 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d17164, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d17164, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19970 (p : Pattern) (guard : d17167 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d17167, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19931 p hg
    simpa only [d17167, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19971 (p : Pattern) (guard : d17168 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19969 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19970 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19972 (p : Pattern) (guard : d17171 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d17171, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19942 p hg
    simpa only [d17171, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19973 (p : Pattern) (guard : d17172 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19972 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19974 (p : Pattern) (guard : d17173 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19971 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19973 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19975 (p : Pattern) (guard : d17174 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19974 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19976 (p : Pattern) (guard : d17175 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19975 p hg
    simpa only [d17175, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17175, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19977 (p : Pattern) (guard : d17176 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d17176, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19976 p hg
    simpa only [d17176, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19978 (p : Pattern) (guard : d17177 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19973 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19979 (p : Pattern) (guard : d17178 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19978 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19980 (p : Pattern) (guard : d17179 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19979 p hg
    simpa only [d17179, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d17179, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19981 (p : Pattern) (guard : d17180 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d17180, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19980 p hg
    simpa only [d17180, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19982 (p : Pattern) (guard : d17181 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19977 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19981 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19983 (p : Pattern) (guard : d17182 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19982 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19984 (p : Pattern) (guard : d17183 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19983 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19985 (p : Pattern) (guard : d17184 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17183 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19984 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19986 (p : Pattern) (guard : d17185 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19981 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19987 (p : Pattern) (guard : d17186 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19986 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19988 (p : Pattern) (guard : d17187 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19987 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19989 (p : Pattern) (guard : d17188 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17187 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19988 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19990 (p : Pattern) (guard : d17189 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17184 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19985 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19989 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19991 (p : Pattern) (guard : d17190 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17189 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19992 (p : Pattern) (guard : d17191 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17190 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19991 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19993 (p : Pattern) (guard : d17192 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17191 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19994 (p : Pattern) (guard : d17193 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17192 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19993 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19995 (p : Pattern) (guard : d17197 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17183 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19955 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19996 (p : Pattern) (guard : d17198 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17187 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19959 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19997 (p : Pattern) (guard : d17199 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17197 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19995 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17198 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19998 (p : Pattern) (guard : d17200 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17199 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19997 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19999 (p : Pattern) (guard : d17201 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17200 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19998 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
