import NetHack.Soko22Hazard87.Compare062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15750 (p : Pattern) (guard : d16880 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16879 p = 1 := by simpa only [d16880, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15749 p hg
    simpa only [d16880, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16880, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16880, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15751 (p : Pattern) (guard : d16881 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16881, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16881, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16880 p = 1 := by simpa only [d16881, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15750 p hg
    simpa only [d16881, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15752 (p : Pattern) (guard : d16882 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16876 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15746 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16881 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15751 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15753 (p : Pattern) (guard : d16883 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16882 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15752 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15754 (p : Pattern) (guard : d16884 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16883 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15753 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15755 (p : Pattern) (guard : d16958 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16884 p = 1 := by simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15754 p hg
    simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15756 (p : Pattern) (guard : d1584 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15757 (p : Pattern) (guard : d1585 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15756 p hg
    simpa only [d1585, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1585, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15758 (p : Pattern) (guard : d1588 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15757 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15759 (p : Pattern) (guard : d15171 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15737 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15760 (p : Pattern) (guard : d16803 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15728 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15759 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15761 (p : Pattern) (guard : d16804 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16804, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15760 p hg
    simpa only [d16804, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15762 (p : Pattern) (guard : d16805 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16805, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15761 p hg
    simpa only [d16805, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15763 (p : Pattern) (guard : d16806 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15762 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15764 (p : Pattern) (guard : d16811 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15763 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15765 (p : Pattern) (guard : d16812 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15764 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15766 (p : Pattern) (guard : d16813 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15765 p hg
    simpa only [d16813, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16813, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15767 (p : Pattern) (guard : d16814 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15766 p hg
    simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15768 (p : Pattern) (guard : d16886 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16881 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15751 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15767 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15769 (p : Pattern) (guard : d16887 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16886 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15768 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15770 (p : Pattern) (guard : d16888 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16887 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15769 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15771 (p : Pattern) (guard : d16959 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16888 p = 1 := by simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15770 p hg
    simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15772 (p : Pattern) (guard : d16960 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16958 p = 1 := by simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16959 p = 1 := by simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15771 p hg
    simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15773 (p : Pattern) (guard : d128358 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16960 p = 1 := by simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15772 p hg
    simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15774 (p : Pattern) (guard : d13287 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15775 (p : Pattern) (guard : d16929 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15728 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13287 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15774 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15776 (p : Pattern) (guard : d16930 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16930, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16930, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16929 p = 1 := by simpa only [d16930, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15775 p hg
    simpa only [d16930, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15777 (p : Pattern) (guard : d16931 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16931, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16931, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16930 p = 1 := by simpa only [d16931, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d16931, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15778 (p : Pattern) (guard : d16932 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16931 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15777 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15779 (p : Pattern) (guard : d16933 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15742 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16932 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15778 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15780 (p : Pattern) (guard : d16934 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16933 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15779 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15781 (p : Pattern) (guard : d16935 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16934 p = 1 := by simpa only [d16935, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15780 p hg
    simpa only [d16935, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16935, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16935, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15782 (p : Pattern) (guard : d16936 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16936, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16936, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16935 p = 1 := by simpa only [d16936, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15781 p hg
    simpa only [d16936, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15783 (p : Pattern) (guard : d16937 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16936 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15782 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15784 (p : Pattern) (guard : d16938 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16937 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15783 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15785 (p : Pattern) (guard : d16939 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16938 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15784 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15786 (p : Pattern) (guard : d16965 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16939 p = 1 := by simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15785 p hg
    simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15787 (p : Pattern) (guard : d16966 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16965 p = 1 := by simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15786 p hg
    simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15788 (p : Pattern) (guard : d16967 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16966 p = 1 := by simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15787 p hg
    simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15789 (p : Pattern) (guard : d128359 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128358 p = 1 := by simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15773 p hg
    simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16967 p = 1 := by simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15788 p hg
    simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15790 (p : Pattern) (guard : d128367 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128359 p = 1 := by simpa only [d128367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15789 p hg
    simpa only [d128367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15791 (p : Pattern) (guard : d128368 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128367 p = 1 := by simpa only [d128368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15790 p hg
    simpa only [d128368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15792 (p : Pattern) (guard : d128369 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128369, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128369, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128368 p = 1 := by simpa only [d128369, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15791 p hg
    simpa only [d128369, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15793 (p : Pattern) (guard : d128370 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128369 p = 1 := by simpa only [d128370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15792 p hg
    simpa only [d128370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15794 (p : Pattern) (guard : d16819 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15767 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15795 (p : Pattern) (guard : d16820 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15794 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15796 (p : Pattern) (guard : d16821 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15795 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15797 (p : Pattern) (guard : d16832 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16821 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15796 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15798 (p : Pattern) (guard : d16984 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16832 p = 1 := by simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15797 p hg
    simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15799 (p : Pattern) (guard : d16985 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16984 p = 1 := by simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15798 p hg
    simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15800 (p : Pattern) (guard : d16986 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16985 p = 1 := by simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15799 p hg
    simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15801 (p : Pattern) (guard : d16987 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16986 p = 1 := by simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15800 p hg
    simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15802 (p : Pattern) (guard : d16988 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16987 p = 1 := by simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15801 p hg
    simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15803 (p : Pattern) (guard : d16998 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16998, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16998, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16988 p = 1 := by simpa only [d16998, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15802 p hg
    simpa only [d16998, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15804 (p : Pattern) (guard : d16999 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d16999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16998 p = 1 := by simpa only [d16999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15803 p hg
    simpa only [d16999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15805 (p : Pattern) (guard : d128371 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128370 p = 1 := by simpa only [d128371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15793 p hg
    simpa only [d128371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16999 p = 1 := by simpa only [d128371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15804 p hg
    simpa only [d128371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15806 (p : Pattern) (guard : d128372 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128371 p = 1 := by simpa only [d128372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15805 p hg
    simpa only [d128372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15807 (p : Pattern) (guard : d128373 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128372 p = 1 := by simpa only [d128373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d128373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15808 (p : Pattern) (guard : d128374 p = 1) : d48359 p ≤ (1 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128366 p = 1 := by simpa only [d128374, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15690 p hg
    simpa only [d128374, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128373 p = 1 := by simpa only [d128374, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15807 p hg
    simpa only [d128374, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15809 (p : Pattern) (guard : d1855 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15810 (p : Pattern) (guard : d1856 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1855 p = 1 := by simpa only [d1856, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15809 p hg
    simpa only [d1856, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1856, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1856, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15811 (p : Pattern) (guard : d17006 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15812 (p : Pattern) (guard : d17007 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17006 p = 1 := by simpa only [d17007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15811 p hg
    simpa only [d17007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d17007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15813 (p : Pattern) (guard : d17008 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1856 p = 1 := by simpa only [d17008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15810 p hg
    simpa only [d17008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17007 p = 1 := by simpa only [d17008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15812 p hg
    simpa only [d17008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15814 (p : Pattern) (guard : d15382 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15815 (p : Pattern) (guard : d15383 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15382 p = 1 := by simpa only [d15383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15814 p hg
    simpa only [d15383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d15383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15816 (p : Pattern) (guard : d15389 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15817 (p : Pattern) (guard : d15390 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15389 p = 1 := by simpa only [d15390, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15816 p hg
    simpa only [d15390, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15390, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d15390, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15818 (p : Pattern) (guard : d17009 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15383 p = 1 := by simpa only [d17009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15815 p hg
    simpa only [d17009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15390 p = 1 := by simpa only [d17009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15817 p hg
    simpa only [d17009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15819 (p : Pattern) (guard : d17010 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17008 p = 1 := by simpa only [d17010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15813 p hg
    simpa only [d17010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17009 p = 1 := by simpa only [d17010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15818 p hg
    simpa only [d17010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15820 (p : Pattern) (guard : d1859 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15821 (p : Pattern) (guard : d1860 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1859 p = 1 := by simpa only [d1860, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15820 p hg
    simpa only [d1860, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1860, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1860, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15822 (p : Pattern) (guard : d17013 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15823 (p : Pattern) (guard : d17014 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17013 p = 1 := by simpa only [d17014, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15822 p hg
    simpa only [d17014, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17014, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d17014, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15824 (p : Pattern) (guard : d17015 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1860 p = 1 := by simpa only [d17015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15821 p hg
    simpa only [d17015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17014 p = 1 := by simpa only [d17015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15823 p hg
    simpa only [d17015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15825 (p : Pattern) (guard : d15399 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15826 (p : Pattern) (guard : d15400 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15399 p = 1 := by simpa only [d15400, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15825 p hg
    simpa only [d15400, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15400, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d15400, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15827 (p : Pattern) (guard : d17016 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15390 p = 1 := by simpa only [d17016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15817 p hg
    simpa only [d17016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15400 p = 1 := by simpa only [d17016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15826 p hg
    simpa only [d17016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15828 (p : Pattern) (guard : d17017 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17015 p = 1 := by simpa only [d17017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15824 p hg
    simpa only [d17017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17016 p = 1 := by simpa only [d17017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15827 p hg
    simpa only [d17017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15829 (p : Pattern) (guard : d17018 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17010 p = 1 := by simpa only [d17018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15819 p hg
    simpa only [d17018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17017 p = 1 := by simpa only [d17018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15828 p hg
    simpa only [d17018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15830 (p : Pattern) (guard : d17019 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17019, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17019, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17018 p = 1 := by simpa only [d17019, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15829 p hg
    simpa only [d17019, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15831 (p : Pattern) (guard : d17020 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17020, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17020, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17019 p = 1 := by simpa only [d17020, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15830 p hg
    simpa only [d17020, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15832 (p : Pattern) (guard : d13488 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15833 (p : Pattern) (guard : d13489 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13488 p = 1 := by simpa only [d13489, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15832 p hg
    simpa only [d13489, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13489, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d13489, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15834 (p : Pattern) (guard : d17021 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13489 p = 1 := by simpa only [d17021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15833 p hg
    simpa only [d17021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15400 p = 1 := by simpa only [d17021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15826 p hg
    simpa only [d17021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15835 (p : Pattern) (guard : d15401 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15400 p = 1 := by simpa only [d15401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15826 p hg
    simpa only [d15401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d15401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15836 (p : Pattern) (guard : d17022 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17021 p = 1 := by simpa only [d17022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15834 p hg
    simpa only [d17022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15401 p = 1 := by simpa only [d17022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15835 p hg
    simpa only [d17022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15837 (p : Pattern) (guard : d17023 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17017 p = 1 := by simpa only [d17023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15828 p hg
    simpa only [d17023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17022 p = 1 := by simpa only [d17023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15836 p hg
    simpa only [d17023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15838 (p : Pattern) (guard : d17024 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17024, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17024, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17023 p = 1 := by simpa only [d17024, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15837 p hg
    simpa only [d17024, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15839 (p : Pattern) (guard : d17025 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17025, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17025, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17024 p = 1 := by simpa only [d17025, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15838 p hg
    simpa only [d17025, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15840 (p : Pattern) (guard : d17026 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17020 p = 1 := by simpa only [d17026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15831 p hg
    simpa only [d17026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17025 p = 1 := by simpa only [d17026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15839 p hg
    simpa only [d17026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15841 (p : Pattern) (guard : d1864 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15842 (p : Pattern) (guard : d1865 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1864 p = 1 := by simpa only [d1865, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15841 p hg
    simpa only [d1865, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1865, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1865, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15843 (p : Pattern) (guard : d17029 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15844 (p : Pattern) (guard : d17030 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17029 p = 1 := by simpa only [d17030, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15843 p hg
    simpa only [d17030, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17030, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d17030, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15845 (p : Pattern) (guard : d17031 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1865 p = 1 := by simpa only [d17031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15842 p hg
    simpa only [d17031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17030 p = 1 := by simpa only [d17031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15844 p hg
    simpa only [d17031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15846 (p : Pattern) (guard : d17032 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17031 p = 1 := by simpa only [d17032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15845 p hg
    simpa only [d17032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15401 p = 1 := by simpa only [d17032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15835 p hg
    simpa only [d17032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15847 (p : Pattern) (guard : d17033 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17017 p = 1 := by simpa only [d17033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15828 p hg
    simpa only [d17033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17032 p = 1 := by simpa only [d17033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15846 p hg
    simpa only [d17033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15848 (p : Pattern) (guard : d17034 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17034, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17034, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17033 p = 1 := by simpa only [d17034, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15847 p hg
    simpa only [d17034, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15849 (p : Pattern) (guard : d17035 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17035, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17035, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17034 p = 1 := by simpa only [d17035, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15848 p hg
    simpa only [d17035, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15850 (p : Pattern) (guard : d6498 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15851 (p : Pattern) (guard : d6499 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6498 p = 1 := by simpa only [d6499, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15850 p hg
    simpa only [d6499, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6499, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d6499, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15852 (p : Pattern) (guard : d6500 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6499 p = 1 := by simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15851 p hg
    simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15853 (p : Pattern) (guard : d15414 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15854 (p : Pattern) (guard : d15415 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15414 p = 1 := by simpa only [d15415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15853 p hg
    simpa only [d15415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d15415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15855 (p : Pattern) (guard : d15416 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15415 p = 1 := by simpa only [d15416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15854 p hg
    simpa only [d15416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d15416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15856 (p : Pattern) (guard : d15417 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6500 p = 1 := by simpa only [d15417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15852 p hg
    simpa only [d15417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15416 p = 1 := by simpa only [d15417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15855 p hg
    simpa only [d15417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15857 (p : Pattern) (guard : d17036 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17032 p = 1 := by simpa only [d17036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15846 p hg
    simpa only [d17036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15417 p = 1 := by simpa only [d17036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15856 p hg
    simpa only [d17036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15858 (p : Pattern) (guard : d17037 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17037, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17037, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17036 p = 1 := by simpa only [d17037, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15857 p hg
    simpa only [d17037, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15859 (p : Pattern) (guard : d17038 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17038, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17038, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17037 p = 1 := by simpa only [d17038, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15858 p hg
    simpa only [d17038, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15860 (p : Pattern) (guard : d17039 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17035 p = 1 := by simpa only [d17039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15849 p hg
    simpa only [d17039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17038 p = 1 := by simpa only [d17039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15859 p hg
    simpa only [d17039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15861 (p : Pattern) (guard : d17040 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17026 p = 1 := by simpa only [d17040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15840 p hg
    simpa only [d17040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17039 p = 1 := by simpa only [d17040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15860 p hg
    simpa only [d17040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15862 (p : Pattern) (guard : d17041 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17040 p = 1 := by simpa only [d17041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15861 p hg
    simpa only [d17041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15863 (p : Pattern) (guard : d17042 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17041 p = 1 := by simpa only [d17042, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15862 p hg
    simpa only [d17042, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17042, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d17042, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15864 (p : Pattern) (guard : d17043 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17043, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17043, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17042 p = 1 := by simpa only [d17043, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15863 p hg
    simpa only [d17043, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15865 (p : Pattern) (guard : d17044 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17038 p = 1 := by simpa only [d17044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15859 p hg
    simpa only [d17044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15866 (p : Pattern) (guard : d17045 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17039 p = 1 := by simpa only [d17045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15860 p hg
    simpa only [d17045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17044 p = 1 := by simpa only [d17045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15865 p hg
    simpa only [d17045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15867 (p : Pattern) (guard : d17046 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17045 p = 1 := by simpa only [d17046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15866 p hg
    simpa only [d17046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15868 (p : Pattern) (guard : d17047 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17046 p = 1 := by simpa only [d17047, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15867 p hg
    simpa only [d17047, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17047, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d17047, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15869 (p : Pattern) (guard : d17048 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17048, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17048, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17047 p = 1 := by simpa only [d17048, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15868 p hg
    simpa only [d17048, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15870 (p : Pattern) (guard : d17049 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17043 p = 1 := by simpa only [d17049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15864 p hg
    simpa only [d17049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17048 p = 1 := by simpa only [d17049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15869 p hg
    simpa only [d17049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15871 (p : Pattern) (guard : d17050 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17049 p = 1 := by simpa only [d17050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15870 p hg
    simpa only [d17050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15872 (p : Pattern) (guard : d17051 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17050 p = 1 := by simpa only [d17051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15871 p hg
    simpa only [d17051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15873 (p : Pattern) (guard : d17052 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17051 p = 1 := by simpa only [d17052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15872 p hg
    simpa only [d17052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15874 (p : Pattern) (guard : d1870 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare15875 (p : Pattern) (guard : d1871 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1870 p = 1 := by simpa only [d1871, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15874 p hg
    simpa only [d1871, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1871, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1871, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15876 (p : Pattern) (guard : d1877 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1871 p = 1 := by simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15875 p hg
    simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15877 (p : Pattern) (guard : d15435 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1877 p = 1 := by simpa only [d15435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15876 p hg
    simpa only [d15435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15416 p = 1 := by simpa only [d15435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15855 p hg
    simpa only [d15435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15878 (p : Pattern) (guard : d17053 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17032 p = 1 := by simpa only [d17053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15846 p hg
    simpa only [d17053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15435 p = 1 := by simpa only [d17053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15877 p hg
    simpa only [d17053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15879 (p : Pattern) (guard : d17054 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17054, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17054, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17053 p = 1 := by simpa only [d17054, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15878 p hg
    simpa only [d17054, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15880 (p : Pattern) (guard : d17055 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17055, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17055, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17054 p = 1 := by simpa only [d17055, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15879 p hg
    simpa only [d17055, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15881 (p : Pattern) (guard : d17056 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17055 p = 1 := by simpa only [d17056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15880 p hg
    simpa only [d17056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15882 (p : Pattern) (guard : d17057 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17056 p = 1 := by simpa only [d17057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15881 p hg
    simpa only [d17057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15883 (p : Pattern) (guard : d17058 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17057 p = 1 := by simpa only [d17058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15882 p hg
    simpa only [d17058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15884 (p : Pattern) (guard : d17059 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17058 p = 1 := by simpa only [d17059, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15883 p hg
    simpa only [d17059, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17059, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d17059, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15885 (p : Pattern) (guard : d17060 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17060, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17060, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17059 p = 1 := by simpa only [d17060, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15884 p hg
    simpa only [d17060, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15886 (p : Pattern) (guard : d17061 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17048 p = 1 := by simpa only [d17061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15869 p hg
    simpa only [d17061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17060 p = 1 := by simpa only [d17061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15885 p hg
    simpa only [d17061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15887 (p : Pattern) (guard : d17062 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17061 p = 1 := by simpa only [d17062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15886 p hg
    simpa only [d17062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15888 (p : Pattern) (guard : d17063 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17062 p = 1 := by simpa only [d17063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15887 p hg
    simpa only [d17063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15889 (p : Pattern) (guard : d17064 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17063 p = 1 := by simpa only [d17064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15888 p hg
    simpa only [d17064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15890 (p : Pattern) (guard : d17065 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17052 p = 1 := by simpa only [d17065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15873 p hg
    simpa only [d17065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17064 p = 1 := by simpa only [d17065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15889 p hg
    simpa only [d17065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15891 (p : Pattern) (guard : d128375 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17065 p = 1 := by simpa only [d128375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15890 p hg
    simpa only [d128375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15892 (p : Pattern) (guard : d13516 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1877 p = 1 := by simpa only [d13516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15876 p hg
    simpa only [d13516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d13516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15893 (p : Pattern) (guard : d17108 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17032 p = 1 := by simpa only [d17108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15846 p hg
    simpa only [d17108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13516 p = 1 := by simpa only [d17108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15892 p hg
    simpa only [d17108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15894 (p : Pattern) (guard : d17109 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17109, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17109, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17108 p = 1 := by simpa only [d17109, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15893 p hg
    simpa only [d17109, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15895 (p : Pattern) (guard : d17110 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17110, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17110, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17109 p = 1 := by simpa only [d17110, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15894 p hg
    simpa only [d17110, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15896 (p : Pattern) (guard : d17111 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17110 p = 1 := by simpa only [d17111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15895 p hg
    simpa only [d17111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15897 (p : Pattern) (guard : d17112 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17039 p = 1 := by simpa only [d17112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15860 p hg
    simpa only [d17112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17111 p = 1 := by simpa only [d17112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15896 p hg
    simpa only [d17112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15898 (p : Pattern) (guard : d17113 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17112 p = 1 := by simpa only [d17113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15897 p hg
    simpa only [d17113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15899 (p : Pattern) (guard : d17114 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17113 p = 1 := by simpa only [d17114, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15898 p hg
    simpa only [d17114, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17114, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d17114, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15900 (p : Pattern) (guard : d17115 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17115, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17115, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17114 p = 1 := by simpa only [d17115, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15899 p hg
    simpa only [d17115, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15901 (p : Pattern) (guard : d17116 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17115 p = 1 := by simpa only [d17116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15900 p hg
    simpa only [d17116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15902 (p : Pattern) (guard : d17117 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17116 p = 1 := by simpa only [d17117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15901 p hg
    simpa only [d17117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15903 (p : Pattern) (guard : d17118 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17117 p = 1 := by simpa only [d17118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15902 p hg
    simpa only [d17118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15904 (p : Pattern) (guard : d17119 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17118 p = 1 := by simpa only [d17119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15903 p hg
    simpa only [d17119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15905 (p : Pattern) (guard : d17120 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17119 p = 1 := by simpa only [d17120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15904 p hg
    simpa only [d17120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15906 (p : Pattern) (guard : d17121 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17120 p = 1 := by simpa only [d17121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15905 p hg
    simpa only [d17121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15907 (p : Pattern) (guard : d128376 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128375 p = 1 := by simpa only [d128376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15891 p hg
    simpa only [d128376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17121 p = 1 := by simpa only [d128376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15906 p hg
    simpa only [d128376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15908 (p : Pattern) (guard : d128377 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128376 p = 1 := by simpa only [d128377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15907 p hg
    simpa only [d128377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15909 (p : Pattern) (guard : d128378 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128377 p = 1 := by simpa only [d128378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15908 p hg
    simpa only [d128378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15910 (p : Pattern) (guard : d128379 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128379, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128379, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128378 p = 1 := by simpa only [d128379, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15909 p hg
    simpa only [d128379, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15911 (p : Pattern) (guard : d128380 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128379 p = 1 := by simpa only [d128380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15910 p hg
    simpa only [d128380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15912 (p : Pattern) (guard : d17127 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17060 p = 1 := by simpa only [d17127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15885 p hg
    simpa only [d17127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15913 (p : Pattern) (guard : d17128 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17127 p = 1 := by simpa only [d17128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15912 p hg
    simpa only [d17128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15914 (p : Pattern) (guard : d17129 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17128 p = 1 := by simpa only [d17129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15913 p hg
    simpa only [d17129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15915 (p : Pattern) (guard : d17130 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17129 p = 1 := by simpa only [d17130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15914 p hg
    simpa only [d17130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15916 (p : Pattern) (guard : d17131 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17130 p = 1 := by simpa only [d17131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15915 p hg
    simpa only [d17131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15917 (p : Pattern) (guard : d17132 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17131 p = 1 := by simpa only [d17132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15916 p hg
    simpa only [d17132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15918 (p : Pattern) (guard : d17133 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17132 p = 1 := by simpa only [d17133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15917 p hg
    simpa only [d17133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15919 (p : Pattern) (guard : d17134 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17133 p = 1 := by simpa only [d17134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15918 p hg
    simpa only [d17134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15920 (p : Pattern) (guard : d17135 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17134 p = 1 := by simpa only [d17135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15919 p hg
    simpa only [d17135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15921 (p : Pattern) (guard : d17136 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17136, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17136, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17135 p = 1 := by simpa only [d17136, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15920 p hg
    simpa only [d17136, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15922 (p : Pattern) (guard : d17137 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d17137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17136 p = 1 := by simpa only [d17137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d17137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15923 (p : Pattern) (guard : d128381 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128380 p = 1 := by simpa only [d128381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15911 p hg
    simpa only [d128381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17137 p = 1 := by simpa only [d128381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15922 p hg
    simpa only [d128381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15924 (p : Pattern) (guard : d128382 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128381 p = 1 := by simpa only [d128382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15923 p hg
    simpa only [d128382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15925 (p : Pattern) (guard : d128383 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128382 p = 1 := by simpa only [d128383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15924 p hg
    simpa only [d128383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15926 (p : Pattern) (guard : d128384 p = 1) : d48387 p ≤ (1 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128383 p = 1 := by simpa only [d128384, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15925 p hg
    simpa only [d128384, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128384, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d128384, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15927 (p : Pattern) (guard : d128385 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128374 p = 1 := by simpa only [d128385, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15808 p hg
    simpa only [d128385, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128384 p = 1 := by simpa only [d128385, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15926 p hg
    simpa only [d128385, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15928 (p : Pattern) (guard : d128386 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128385 p = 1 := by simpa only [d128386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15927 p hg
    simpa only [d128386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15929 (p : Pattern) (guard : d128387 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128386 p = 1 := by simpa only [d128387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15928 p hg
    simpa only [d128387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15930 (p : Pattern) (guard : d128388 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128387 p = 1 := by simpa only [d128388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15929 p hg
    simpa only [d128388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15931 (p : Pattern) (guard : d128389 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128388 p = 1 := by simpa only [d128389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15930 p hg
    simpa only [d128389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15932 (p : Pattern) (guard : d128390 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128389 p = 1 := by simpa only [d128390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15931 p hg
    simpa only [d128390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15933 (p : Pattern) (guard : d128391 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128390 p = 1 := by simpa only [d128391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15932 p hg
    simpa only [d128391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15934 (p : Pattern) (guard : d128392 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128391 p = 1 := by simpa only [d128392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d128392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15935 (p : Pattern) (guard : d128393 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128392 p = 1 := by simpa only [d128393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15934 p hg
    simpa only [d128393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15936 (p : Pattern) (guard : d128394 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128393 p = 1 := by simpa only [d128394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15935 p hg
    simpa only [d128394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15937 (p : Pattern) (guard : d128395 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d128352 p = 1 := by simpa only [d128395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15411 p hg
    simpa only [d128395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128394 p = 1 := by simpa only [d128395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15936 p hg
    simpa only [d128395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15938 (p : Pattern) (guard : d2037 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15939 (p : Pattern) (guard : d2038 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15938 p hg
    simpa only [d2038, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d2038, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15940 (p : Pattern) (guard : d17153 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15941 (p : Pattern) (guard : d17154 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15940 p hg
    simpa only [d17154, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d17154, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15942 (p : Pattern) (guard : d17155 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15939 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15941 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15943 (p : Pattern) (guard : d13675 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15944 (p : Pattern) (guard : d13676 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15943 p hg
    simpa only [d13676, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d13676, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15945 (p : Pattern) (guard : d15548 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15946 (p : Pattern) (guard : d15549 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15945 p hg
    simpa only [d15549, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d15549, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15947 (p : Pattern) (guard : d17156 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15944 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15946 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15948 (p : Pattern) (guard : d17157 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15942 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15947 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15949 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15950 (p : Pattern) (guard : d2056 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15949 p hg
    simpa only [d2056, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d2056, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15951 (p : Pattern) (guard : d17158 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15952 (p : Pattern) (guard : d17159 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d17159, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d17159, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15953 (p : Pattern) (guard : d17160 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15950 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15952 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15954 (p : Pattern) (guard : d15550 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15946 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15955 (p : Pattern) (guard : d17161 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15953 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15954 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15956 (p : Pattern) (guard : d17162 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15948 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15955 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15957 (p : Pattern) (guard : d17163 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d17163, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15956 p hg
    simpa only [d17163, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15958 (p : Pattern) (guard : d17164 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d17164, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15957 p hg
    simpa only [d17164, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15959 (p : Pattern) (guard : d5249 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15960 (p : Pattern) (guard : d5250 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15959 p hg
    simpa only [d5250, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d5250, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15961 (p : Pattern) (guard : d5251 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15960 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15962 (p : Pattern) (guard : d15555 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15963 (p : Pattern) (guard : d15556 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15962 p hg
    simpa only [d15556, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d15556, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15964 (p : Pattern) (guard : d15557 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15963 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15965 (p : Pattern) (guard : d15558 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15961 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15964 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15966 (p : Pattern) (guard : d17165 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15955 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15965 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15967 (p : Pattern) (guard : d17166 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d17166, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15966 p hg
    simpa only [d17166, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15968 (p : Pattern) (guard : d17167 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d17167, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15967 p hg
    simpa only [d17167, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15969 (p : Pattern) (guard : d17168 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15958 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15968 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15970 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15971 (p : Pattern) (guard : d2068 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15970 p hg
    simpa only [d2068, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d2068, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15972 (p : Pattern) (guard : d2071 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15971 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15973 (p : Pattern) (guard : d15563 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15972 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15964 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15974 (p : Pattern) (guard : d17169 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15955 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15973 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15975 (p : Pattern) (guard : d17170 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d17170, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15974 p hg
    simpa only [d17170, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15976 (p : Pattern) (guard : d17171 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d17171, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15975 p hg
    simpa only [d17171, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15977 (p : Pattern) (guard : d17172 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15978 (p : Pattern) (guard : d17173 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15969 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15977 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15979 (p : Pattern) (guard : d17174 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15978 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15980 (p : Pattern) (guard : d17175 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d17175, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17175, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15981 (p : Pattern) (guard : d17176 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17176, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15980 p hg
    simpa only [d17176, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15982 (p : Pattern) (guard : d17177 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15977 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15983 (p : Pattern) (guard : d17178 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15982 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15984 (p : Pattern) (guard : d17179 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15983 p hg
    simpa only [d17179, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d17179, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15985 (p : Pattern) (guard : d17180 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17180, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d17180, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15986 (p : Pattern) (guard : d17181 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15981 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15985 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15987 (p : Pattern) (guard : d17182 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15986 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15988 (p : Pattern) (guard : d17183 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15987 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15989 (p : Pattern) (guard : d17184 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17183 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15988 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15990 (p : Pattern) (guard : d17185 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15985 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15991 (p : Pattern) (guard : d17186 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15990 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15992 (p : Pattern) (guard : d17187 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15991 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15993 (p : Pattern) (guard : d17188 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17187 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15992 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15994 (p : Pattern) (guard : d17189 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17184 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15989 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15993 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15995 (p : Pattern) (guard : d17190 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17189 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15994 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15996 (p : Pattern) (guard : d17191 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17190 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15995 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15997 (p : Pattern) (guard : d17192 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17191 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15996 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15998 (p : Pattern) (guard : d17193 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17192 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15999 (p : Pattern) (guard : d17194 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17193 p = 1 := by simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15998 p hg
    simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
