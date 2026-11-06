import NetHack.Soko22Hazard87.Compare163
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41000 (p : Pattern) (guard : d221495 p = 1) : d50658 p ≤ (0 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221494 p = 1 := by simpa only [d221495, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40999 p hg
    simpa only [d221495, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221495, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d221495, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41001 (p : Pattern) (guard : d221496 p = 1) : d50659 p ≤ (0 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221496, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40687 p hg
    simpa only [d221496, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221495 p = 1 := by simpa only [d221496, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41000 p hg
    simpa only [d221496, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41002 (p : Pattern) (guard : d221497 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221496 p = 1 := by simpa only [d221497, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41001 p hg
    simpa only [d221497, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221497, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40702 p hg
    simpa only [d221497, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41003 (p : Pattern) (guard : d221498 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221497 p = 1 := by simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41002 p hg
    simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40686 p hg
    simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41004 (p : Pattern) (guard : d324894 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324889 p = 1 := by simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40993 p hg
    simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221498 p = 1 := by simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41003 p hg
    simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41005 (p : Pattern) (guard : d324895 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324890 p = 1 := by simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40994 p hg
    simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324894 p = 1 := by simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41004 p hg
    simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41006 (p : Pattern) (guard : d324896 p = 1) : d50664 p ≤ (0 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324896, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40685 p hg
    simpa only [d324896, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324895 p = 1 := by simpa only [d324896, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41005 p hg
    simpa only [d324896, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41007 (p : Pattern) (guard : d324897 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324897, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40684 p hg
    simpa only [d324897, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324896 p = 1 := by simpa only [d324897, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41006 p hg
    simpa only [d324897, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41008 (p : Pattern) (guard : d324898 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324893 p = 1 := by simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40997 p hg
    simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324897 p = 1 := by simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41007 p hg
    simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41009 (p : Pattern) (guard : d324899 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324897 p = 1 := by simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41007 p hg
    simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41010 (p : Pattern) (guard : d324900 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324898 p = 1 := by simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41008 p hg
    simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324899 p = 1 := by simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41009 p hg
    simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41011 (p : Pattern) (guard : d324901 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324900 p = 1 := by simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41010 p hg
    simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41012 (p : Pattern) (guard : d324902 p = 1) : d50673 p ≤ (0 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324901 p = 1 := by simpa only [d324902, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41011 p hg
    simpa only [d324902, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324902, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40740 p hg
    simpa only [d324902, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41013 (p : Pattern) (guard : d324903 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324903, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40683 p hg
    simpa only [d324903, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324902 p = 1 := by simpa only [d324903, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41012 p hg
    simpa only [d324903, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41014 (p : Pattern) (guard : d324904 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324899 p = 1 := by simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41009 p hg
    simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41015 (p : Pattern) (guard : d324905 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324904 p = 1 := by simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41014 p hg
    simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41016 (p : Pattern) (guard : d324906 p = 1) : d50673 p ≤ (0 : Int) + d324516 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324905 p = 1 := by simpa only [d324906, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41015 p hg
    simpa only [d324906, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324906, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40740 p hg
    simpa only [d324906, d50673, d324516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41017 (p : Pattern) (guard : d324907 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324907, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40683 p hg
    simpa only [d324907, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324906 p = 1 := by simpa only [d324907, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41016 p hg
    simpa only [d324907, d50674, d324517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41018 (p : Pattern) (guard : d324908 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324903 p = 1 := by simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41013 p hg
    simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324907 p = 1 := by simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41017 p hg
    simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41019 (p : Pattern) (guard : d324909 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324908 p = 1 := by simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41018 p hg
    simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41020 (p : Pattern) (guard : d324910 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324909 p = 1 := by simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41019 p hg
    simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41021 (p : Pattern) (guard : d324924 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324910 p = 1 := by simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41020 p hg
    simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41022 (p : Pattern) (guard : d324912 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324907 p = 1 := by simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41017 p hg
    simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41023 (p : Pattern) (guard : d324913 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324912 p = 1 := by simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41022 p hg
    simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41024 (p : Pattern) (guard : d324914 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324913 p = 1 := by simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41023 p hg
    simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41025 (p : Pattern) (guard : d324925 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324914 p = 1 := by simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41024 p hg
    simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41026 (p : Pattern) (guard : d324926 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324924 p = 1 := by simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41021 p hg
    simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324925 p = 1 := by simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41025 p hg
    simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41027 (p : Pattern) (guard : d324927 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324926 p = 1 := by simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41026 p hg
    simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41028 (p : Pattern) (guard : d324928 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324927 p = 1 := by simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41027 p hg
    simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41029 (p : Pattern) (guard : d324929 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324928 p = 1 := by simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41028 p hg
    simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41030 (p : Pattern) (guard : d324930 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324929 p = 1 := by simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41029 p hg
    simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41031 (p : Pattern) (guard : d325211 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325211, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d325211, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324930 p = 1 := by simpa only [d325211, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41030 p hg
    simpa only [d325211, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41032 (p : Pattern) (guard : d325212 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d325212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325211 p = 1 := by simpa only [d325212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41031 p hg
    simpa only [d325212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41033 (p : Pattern) (guard : d325213 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 69 with
  | false =>
    have hg : d325212 p = 1 := by simpa only [d325213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41032 p hg
    simpa only [d325213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d325213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41034 (p : Pattern) (guard : d325214 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 51 with
  | false =>
    have hg : d325213 p = 1 := by simpa only [d325214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41033 p hg
    simpa only [d325214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d325214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41035 (p : Pattern) (guard : d325215 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 50 with
  | false =>
    have hg : d325214 p = 1 := by simpa only [d325215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41034 p hg
    simpa only [d325215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d325215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41036 (p : Pattern) (guard : d325216 p = 1) : d50676 p ≤ (0 : Int) + d324519 p := by
  cases selected : p 49 with
  | false =>
    have hg : d325210 p = 1 := by simpa only [d325216, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40966 p hg
    simpa only [d325216, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325215 p = 1 := by simpa only [d325216, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41035 p hg
    simpa only [d325216, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41037 (p : Pattern) (guard : d10055 p = 1) : d49316 p ≤ (0 : Int) + d49316 p := by
  omega
theorem compare41038 (p : Pattern) (guard : d38167 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38167, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d38167, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d38167, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41037 p hg
    simpa only [d38167, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41039 (p : Pattern) (guard : d38168 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d38167 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41038 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41040 (p : Pattern) (guard : d38169 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d38168 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41039 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41041 (p : Pattern) (guard : d38170 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 182 with
  | false =>
    have hg : d38169 p = 1 := by simpa only [d38170, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41040 p hg
    simpa only [d38170, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38170, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40779 p hg
    simpa only [d38170, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41042 (p : Pattern) (guard : d38177 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40772 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38170 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41041 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41043 (p : Pattern) (guard : d38532 p = 1) : d50726 p ≤ (0 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38532, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40771 p hg
    simpa only [d38532, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38177 p = 1 := by simpa only [d38532, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41042 p hg
    simpa only [d38532, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41044 (p : Pattern) (guard : d38178 p = 1) : d50727 p ≤ (0 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d38177 p = 1 := by simpa only [d38178, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40895 p hg
    simpa only [d38178, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38178, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d38178, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41045 (p : Pattern) (guard : d38533 p = 1) : d50728 p ≤ (0 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d38532 p = 1 := by simpa only [d38533, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41043 p hg
    simpa only [d38533, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38178 p = 1 := by simpa only [d38533, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41044 p hg
    simpa only [d38533, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41046 (p : Pattern) (guard : d10055 p = 1) : d49323 p ≤ (0 : Int) + d49323 p := by
  omega
theorem compare41047 (p : Pattern) (guard : d38167 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38167, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d38167, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d38167, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41046 p hg
    simpa only [d38167, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41048 (p : Pattern) (guard : d38168 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d38167 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41047 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41049 (p : Pattern) (guard : d38169 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d38168 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41048 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41050 (p : Pattern) (guard : d38170 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d38169 p = 1 := by simpa only [d38170, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41049 p hg
    simpa only [d38170, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38170, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40792 p hg
    simpa only [d38170, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41051 (p : Pattern) (guard : d38177 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40785 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38170 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41050 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41052 (p : Pattern) (guard : d38178 p = 1) : d50573 p ≤ (0 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d38177 p = 1 := by simpa only [d38178, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41051 p hg
    simpa only [d38178, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38178, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d38178, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41053 (p : Pattern) (guard : d38179 p = 1) : d50574 p ≤ (0 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d38178 p = 1 := by simpa only [d38179, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41052 p hg
    simpa only [d38179, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38179, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d38179, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41054 (p : Pattern) (guard : d38534 p = 1) : d50729 p ≤ (0 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d38533 p = 1 := by simpa only [d38534, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41045 p hg
    simpa only [d38534, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38179 p = 1 := by simpa only [d38534, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41053 p hg
    simpa only [d38534, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41055 (p : Pattern) (guard : d38535 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d38534 p = 1 := by simpa only [d38535, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41054 p hg
    simpa only [d38535, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38535, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40798 p hg
    simpa only [d38535, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41056 (p : Pattern) (guard : d38536 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d38536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38535 p = 1 := by simpa only [d38536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41055 p hg
    simpa only [d38536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41057 (p : Pattern) (guard : d2043 p = 1) : d49316 p ≤ (0 : Int) + d49316 p := by
  omega
theorem compare41058 (p : Pattern) (guard : d221468 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221468, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d221468, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d221468, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41057 p hg
    simpa only [d221468, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41059 (p : Pattern) (guard : d221488 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221468 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41058 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41060 (p : Pattern) (guard : d10406 p = 1) : d49316 p ≤ (0 : Int) + d49316 p := by
  omega
theorem compare41061 (p : Pattern) (guard : d221489 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221489, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d221489, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d221489, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41060 p hg
    simpa only [d221489, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41062 (p : Pattern) (guard : d221490 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221489 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41061 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41063 (p : Pattern) (guard : d221491 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221488 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41059 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41062 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41064 (p : Pattern) (guard : d221492 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221491 p = 1 := by simpa only [d221492, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41063 p hg
    simpa only [d221492, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221492, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40779 p hg
    simpa only [d221492, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41065 (p : Pattern) (guard : d324882 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41041 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221492 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41064 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41066 (p : Pattern) (guard : d325040 p = 1) : d50726 p ≤ (0 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325040, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40771 p hg
    simpa only [d325040, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324882 p = 1 := by simpa only [d325040, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41065 p hg
    simpa only [d325040, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41067 (p : Pattern) (guard : d324883 p = 1) : d50727 p ≤ (0 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324882 p = 1 := by simpa only [d324883, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40909 p hg
    simpa only [d324883, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324883, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d324883, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41068 (p : Pattern) (guard : d325041 p = 1) : d50728 p ≤ (0 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d325040 p = 1 := by simpa only [d325041, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41066 p hg
    simpa only [d325041, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324883 p = 1 := by simpa only [d325041, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41067 p hg
    simpa only [d325041, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41069 (p : Pattern) (guard : d2043 p = 1) : d49323 p ≤ (0 : Int) + d49323 p := by
  omega
theorem compare41070 (p : Pattern) (guard : d221468 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221468, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d221468, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d221468, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41069 p hg
    simpa only [d221468, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41071 (p : Pattern) (guard : d221488 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221468 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41070 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41072 (p : Pattern) (guard : d10406 p = 1) : d49323 p ≤ (0 : Int) + d49323 p := by
  omega
theorem compare41073 (p : Pattern) (guard : d221489 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221489, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d221489, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d221489, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41072 p hg
    simpa only [d221489, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41074 (p : Pattern) (guard : d221490 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221489 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41073 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41075 (p : Pattern) (guard : d221491 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221488 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41071 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41074 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41076 (p : Pattern) (guard : d221492 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221491 p = 1 := by simpa only [d221492, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41075 p hg
    simpa only [d221492, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221492, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40792 p hg
    simpa only [d221492, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41077 (p : Pattern) (guard : d324882 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41050 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221492 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41076 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41078 (p : Pattern) (guard : d324883 p = 1) : d50573 p ≤ (0 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324882 p = 1 := by simpa only [d324883, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41077 p hg
    simpa only [d324883, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324883, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324883, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41079 (p : Pattern) (guard : d324884 p = 1) : d50574 p ≤ (0 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324883 p = 1 := by simpa only [d324884, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41078 p hg
    simpa only [d324884, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324884, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324884, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41080 (p : Pattern) (guard : d325042 p = 1) : d50729 p ≤ (0 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d325041 p = 1 := by simpa only [d325042, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41068 p hg
    simpa only [d325042, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324884 p = 1 := by simpa only [d325042, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41079 p hg
    simpa only [d325042, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41081 (p : Pattern) (guard : d325043 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d325042 p = 1 := by simpa only [d325043, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41080 p hg
    simpa only [d325043, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325043, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40798 p hg
    simpa only [d325043, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41082 (p : Pattern) (guard : d325044 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d38535 p = 1 := by simpa only [d325044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41055 p hg
    simpa only [d325044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325043 p = 1 := by simpa only [d325044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41081 p hg
    simpa only [d325044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41083 (p : Pattern) (guard : d325045 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d38536 p = 1 := by simpa only [d325045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41056 p hg
    simpa only [d325045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325044 p = 1 := by simpa only [d325045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41082 p hg
    simpa only [d325045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41084 (p : Pattern) (guard : d325049 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d325043 p = 1 := by simpa only [d325049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41081 p hg
    simpa only [d325049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d325049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41085 (p : Pattern) (guard : d325050 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d325044 p = 1 := by simpa only [d325050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41082 p hg
    simpa only [d325050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325049 p = 1 := by simpa only [d325050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41084 p hg
    simpa only [d325050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41086 (p : Pattern) (guard : d325051 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d325045 p = 1 := by simpa only [d325051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41083 p hg
    simpa only [d325051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325050 p = 1 := by simpa only [d325051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41085 p hg
    simpa only [d325051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41087 (p : Pattern) (guard : d325052 p = 1) : d50734 p ≤ (0 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325052, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40769 p hg
    simpa only [d325052, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325051 p = 1 := by simpa only [d325052, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41086 p hg
    simpa only [d325052, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41088 (p : Pattern) (guard : d325053 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325053, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40768 p hg
    simpa only [d325053, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325052 p = 1 := by simpa only [d325053, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41087 p hg
    simpa only [d325053, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41089 (p : Pattern) (guard : d221493 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221492 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41064 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40772 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41090 (p : Pattern) (guard : d221734 p = 1) : d50726 p ≤ (0 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221734, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40771 p hg
    simpa only [d221734, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221493 p = 1 := by simpa only [d221734, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41089 p hg
    simpa only [d221734, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41091 (p : Pattern) (guard : d221494 p = 1) : d50727 p ≤ (0 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221493 p = 1 := by simpa only [d221494, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40921 p hg
    simpa only [d221494, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221494, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d221494, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41092 (p : Pattern) (guard : d221735 p = 1) : d50728 p ≤ (0 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221734 p = 1 := by simpa only [d221735, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41090 p hg
    simpa only [d221735, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221494 p = 1 := by simpa only [d221735, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41091 p hg
    simpa only [d221735, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41093 (p : Pattern) (guard : d221493 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221492 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41076 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40785 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41094 (p : Pattern) (guard : d221494 p = 1) : d50573 p ≤ (0 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221493 p = 1 := by simpa only [d221494, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41093 p hg
    simpa only [d221494, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221494, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d221494, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41095 (p : Pattern) (guard : d221495 p = 1) : d50574 p ≤ (0 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221494 p = 1 := by simpa only [d221495, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41094 p hg
    simpa only [d221495, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221495, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d221495, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41096 (p : Pattern) (guard : d221736 p = 1) : d50729 p ≤ (0 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d221735 p = 1 := by simpa only [d221736, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41092 p hg
    simpa only [d221736, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221495 p = 1 := by simpa only [d221736, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41095 p hg
    simpa only [d221736, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41097 (p : Pattern) (guard : d221737 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221736 p = 1 := by simpa only [d221737, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41096 p hg
    simpa only [d221737, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221737, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40798 p hg
    simpa only [d221737, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41098 (p : Pattern) (guard : d221738 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221737 p = 1 := by simpa only [d221738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41097 p hg
    simpa only [d221738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d221738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41099 (p : Pattern) (guard : d325055 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d325049 p = 1 := by simpa only [d325055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41084 p hg
    simpa only [d325055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221738 p = 1 := by simpa only [d325055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41098 p hg
    simpa only [d325055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41100 (p : Pattern) (guard : d325056 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d325050 p = 1 := by simpa only [d325056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41085 p hg
    simpa only [d325056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325055 p = 1 := by simpa only [d325056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41099 p hg
    simpa only [d325056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41101 (p : Pattern) (guard : d325057 p = 1) : d50734 p ≤ (0 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325057, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40769 p hg
    simpa only [d325057, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325056 p = 1 := by simpa only [d325057, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41100 p hg
    simpa only [d325057, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41102 (p : Pattern) (guard : d325058 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325058, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40768 p hg
    simpa only [d325058, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325057 p = 1 := by simpa only [d325058, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41101 p hg
    simpa only [d325058, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41103 (p : Pattern) (guard : d325059 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d325053 p = 1 := by simpa only [d325059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41088 p hg
    simpa only [d325059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325058 p = 1 := by simpa only [d325059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41102 p hg
    simpa only [d325059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41104 (p : Pattern) (guard : d325064 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d325058 p = 1 := by simpa only [d325064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41102 p hg
    simpa only [d325064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d325064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41105 (p : Pattern) (guard : d325065 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d325059 p = 1 := by simpa only [d325065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41103 p hg
    simpa only [d325065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325064 p = 1 := by simpa only [d325065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41104 p hg
    simpa only [d325065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41106 (p : Pattern) (guard : d325066 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d325065 p = 1 := by simpa only [d325066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41105 p hg
    simpa only [d325066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d325066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41107 (p : Pattern) (guard : d325067 p = 1) : d50737 p ≤ (0 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d325066 p = 1 := by simpa only [d325067, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41106 p hg
    simpa only [d325067, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325067, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40852 p hg
    simpa only [d325067, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41108 (p : Pattern) (guard : d325068 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325068, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d325068, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325067 p = 1 := by simpa only [d325068, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41107 p hg
    simpa only [d325068, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41109 (p : Pattern) (guard : d325073 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d325064 p = 1 := by simpa only [d325073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41104 p hg
    simpa only [d325073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d325073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41110 (p : Pattern) (guard : d325074 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d325073 p = 1 := by simpa only [d325074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41109 p hg
    simpa only [d325074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d325074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41111 (p : Pattern) (guard : d325075 p = 1) : d50737 p ≤ (0 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d325074 p = 1 := by simpa only [d325075, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41110 p hg
    simpa only [d325075, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325075, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40852 p hg
    simpa only [d325075, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41112 (p : Pattern) (guard : d325076 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325076, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d325076, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325075 p = 1 := by simpa only [d325076, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41111 p hg
    simpa only [d325076, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41113 (p : Pattern) (guard : d325077 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d325068 p = 1 := by simpa only [d325077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41108 p hg
    simpa only [d325077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325076 p = 1 := by simpa only [d325077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41112 p hg
    simpa only [d325077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41114 (p : Pattern) (guard : d325078 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d325077 p = 1 := by simpa only [d325078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41113 p hg
    simpa only [d325078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41115 (p : Pattern) (guard : d325079 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d325078 p = 1 := by simpa only [d325079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41114 p hg
    simpa only [d325079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41116 (p : Pattern) (guard : d325080 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d325079 p = 1 := by simpa only [d325080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41115 p hg
    simpa only [d325080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41117 (p : Pattern) (guard : d324334 p = 1) : d49323 p ≤ (0 : Int) + d49323 p := by
  omega
theorem compare41118 (p : Pattern) (guard : d325217 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325217, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d325217, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324334 p = 1 := by simpa only [d325217, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41117 p hg
    simpa only [d325217, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41119 (p : Pattern) (guard : d325218 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d325217 p = 1 := by simpa only [d325218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41118 p hg
    simpa only [d325218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d325218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41120 (p : Pattern) (guard : d325219 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d325218 p = 1 := by simpa only [d325219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41119 p hg
    simpa only [d325219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d325219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41074 p hg
    simpa only [d325219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41121 (p : Pattern) (guard : d325220 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d325219 p = 1 := by simpa only [d325220, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41120 p hg
    simpa only [d325220, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325220, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40792 p hg
    simpa only [d325220, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41122 (p : Pattern) (guard : d325221 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d325220 p = 1 := by simpa only [d325221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41121 p hg
    simpa only [d325221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40785 p hg
    simpa only [d325221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41123 (p : Pattern) (guard : d325222 p = 1) : d50573 p ≤ (0 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d325221 p = 1 := by simpa only [d325222, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41122 p hg
    simpa only [d325222, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325222, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d325222, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41124 (p : Pattern) (guard : d325223 p = 1) : d50574 p ≤ (0 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d325222 p = 1 := by simpa only [d325223, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41123 p hg
    simpa only [d325223, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325223, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d325223, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41125 (p : Pattern) (guard : d325224 p = 1) : d50729 p ≤ (0 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d221735 p = 1 := by simpa only [d325224, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41092 p hg
    simpa only [d325224, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325223 p = 1 := by simpa only [d325224, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41124 p hg
    simpa only [d325224, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41126 (p : Pattern) (guard : d325225 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d325224 p = 1 := by simpa only [d325225, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41125 p hg
    simpa only [d325225, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325225, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40798 p hg
    simpa only [d325225, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41127 (p : Pattern) (guard : d325226 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d325225 p = 1 := by simpa only [d325226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41126 p hg
    simpa only [d325226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d325226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41128 (p : Pattern) (guard : d325227 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d325049 p = 1 := by simpa only [d325227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41084 p hg
    simpa only [d325227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325226 p = 1 := by simpa only [d325227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41127 p hg
    simpa only [d325227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41129 (p : Pattern) (guard : d325228 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d325050 p = 1 := by simpa only [d325228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41085 p hg
    simpa only [d325228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325227 p = 1 := by simpa only [d325228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41128 p hg
    simpa only [d325228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41130 (p : Pattern) (guard : d325229 p = 1) : d50734 p ≤ (0 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325229, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40769 p hg
    simpa only [d325229, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325228 p = 1 := by simpa only [d325229, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41129 p hg
    simpa only [d325229, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41131 (p : Pattern) (guard : d325230 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325230, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40768 p hg
    simpa only [d325230, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325229 p = 1 := by simpa only [d325230, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41130 p hg
    simpa only [d325230, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41132 (p : Pattern) (guard : d325231 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d325230 p = 1 := by simpa only [d325231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41131 p hg
    simpa only [d325231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d325231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41133 (p : Pattern) (guard : d325232 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d325231 p = 1 := by simpa only [d325232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41132 p hg
    simpa only [d325232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d325232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41134 (p : Pattern) (guard : d325233 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d325232 p = 1 := by simpa only [d325233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41133 p hg
    simpa only [d325233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d325233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41135 (p : Pattern) (guard : d325234 p = 1) : d50737 p ≤ (0 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d325233 p = 1 := by simpa only [d325234, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41134 p hg
    simpa only [d325234, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325234, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40852 p hg
    simpa only [d325234, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41136 (p : Pattern) (guard : d325235 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325235, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d325235, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325234 p = 1 := by simpa only [d325235, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41135 p hg
    simpa only [d325235, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41137 (p : Pattern) (guard : d325236 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d325235 p = 1 := by simpa only [d325236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41136 p hg
    simpa only [d325236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41138 (p : Pattern) (guard : d325237 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d325236 p = 1 := by simpa only [d325237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41137 p hg
    simpa only [d325237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41139 (p : Pattern) (guard : d325238 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d325237 p = 1 := by simpa only [d325238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41138 p hg
    simpa only [d325238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41140 (p : Pattern) (guard : d325239 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d325238 p = 1 := by simpa only [d325239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41139 p hg
    simpa only [d325239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41141 (p : Pattern) (guard : d325240 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 91 with
  | false =>
    have hg : d325080 p = 1 := by simpa only [d325240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41116 p hg
    simpa only [d325240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325239 p = 1 := by simpa only [d325240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41140 p hg
    simpa only [d325240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41142 (p : Pattern) (guard : d325241 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325240 p = 1 := by simpa only [d325241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41141 p hg
    simpa only [d325241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41143 (p : Pattern) (guard : d325242 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325241 p = 1 := by simpa only [d325242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41142 p hg
    simpa only [d325242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41144 (p : Pattern) (guard : d325243 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325242 p = 1 := by simpa only [d325243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41143 p hg
    simpa only [d325243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41145 (p : Pattern) (guard : d325244 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325243 p = 1 := by simpa only [d325244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41144 p hg
    simpa only [d325244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41146 (p : Pattern) (guard : d325245 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325245, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d325245, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325244 p = 1 := by simpa only [d325245, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41145 p hg
    simpa only [d325245, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41147 (p : Pattern) (guard : d325246 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d325246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325245 p = 1 := by simpa only [d325246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41146 p hg
    simpa only [d325246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41148 (p : Pattern) (guard : d325247 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 69 with
  | false =>
    have hg : d325246 p = 1 := by simpa only [d325247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41147 p hg
    simpa only [d325247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d325247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41149 (p : Pattern) (guard : d325248 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 51 with
  | false =>
    have hg : d325247 p = 1 := by simpa only [d325248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41148 p hg
    simpa only [d325248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d325248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41150 (p : Pattern) (guard : d325249 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 50 with
  | false =>
    have hg : d325248 p = 1 := by simpa only [d325249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41149 p hg
    simpa only [d325249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d325249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41151 (p : Pattern) (guard : d325250 p = 1) : d50822 p ≤ (0 : Int) + d324610 p := by
  cases selected : p 49 with
  | false =>
    have hg : d325249 p = 1 := by simpa only [d325250, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41150 p hg
    simpa only [d325250, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325250, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40877 p hg
    simpa only [d325250, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41152 (p : Pattern) (guard : d325251 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 48 with
  | false =>
    have hg : d325216 p = 1 := by simpa only [d325251, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41036 p hg
    simpa only [d325251, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325250 p = 1 := by simpa only [d325251, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41151 p hg
    simpa only [d325251, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41153 (p : Pattern) (guard : d325252 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325251 p = 1 := by simpa only [d325252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41152 p hg
    simpa only [d325252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41154 (p : Pattern) (guard : d325253 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325252 p = 1 := by simpa only [d325253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41153 p hg
    simpa only [d325253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41155 (p : Pattern) (guard : d325254 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325253 p = 1 := by simpa only [d325254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41154 p hg
    simpa only [d325254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41156 (p : Pattern) (guard : d325255 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325254 p = 1 := by simpa only [d325255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41155 p hg
    simpa only [d325255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41157 (p : Pattern) (guard : d325256 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325255 p = 1 := by simpa only [d325256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41156 p hg
    simpa only [d325256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41158 (p : Pattern) (guard : d325257 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325256 p = 1 := by simpa only [d325257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41157 p hg
    simpa only [d325257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41159 (p : Pattern) (guard : d325258 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325257 p = 1 := by simpa only [d325258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41158 p hg
    simpa only [d325258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41160 (p : Pattern) (guard : d325259 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325258 p = 1 := by simpa only [d325259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41159 p hg
    simpa only [d325259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41161 (p : Pattern) (guard : d325260 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325259 p = 1 := by simpa only [d325260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41160 p hg
    simpa only [d325260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41162 (p : Pattern) (guard : d325261 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325260 p = 1 := by simpa only [d325261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41161 p hg
    simpa only [d325261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41163 (p : Pattern) (guard : d325262 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d325208 p = 1 := by simpa only [d325262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40889 p hg
    simpa only [d325262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325261 p = 1 := by simpa only [d325262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41162 p hg
    simpa only [d325262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41164 (p : Pattern) (guard : d325263 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 260 with
  | false =>
    have hg : d325262 p = 1 := by simpa only [d325263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41163 p hg
    simpa only [d325263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41165 (p : Pattern) (guard : d325264 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 259 with
  | false =>
    have hg : d325263 p = 1 := by simpa only [d325264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41164 p hg
    simpa only [d325264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41166 (p : Pattern) (guard : d325265 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 258 with
  | false =>
    have hg : d325264 p = 1 := by simpa only [d325265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41165 p hg
    simpa only [d325265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41167 (p : Pattern) (guard : d325266 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 257 with
  | false =>
    have hg : d325265 p = 1 := by simpa only [d325266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41166 p hg
    simpa only [d325266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41168 (p : Pattern) (guard : d325267 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 256 with
  | false =>
    have hg : d325266 p = 1 := by simpa only [d325267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41167 p hg
    simpa only [d325267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41169 (p : Pattern) (guard : d325268 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 255 with
  | false =>
    have hg : d325267 p = 1 := by simpa only [d325268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41168 p hg
    simpa only [d325268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41170 (p : Pattern) (guard : d325269 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 254 with
  | false =>
    have hg : d325268 p = 1 := by simpa only [d325269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41169 p hg
    simpa only [d325269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41171 (p : Pattern) (guard : d325270 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 253 with
  | false =>
    have hg : d325269 p = 1 := by simpa only [d325270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41170 p hg
    simpa only [d325270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41172 (p : Pattern) (guard : d325271 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 252 with
  | false =>
    have hg : d325270 p = 1 := by simpa only [d325271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41171 p hg
    simpa only [d325271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41173 (p : Pattern) (guard : d325272 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 251 with
  | false =>
    have hg : d325271 p = 1 := by simpa only [d325272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41172 p hg
    simpa only [d325272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41174 (p : Pattern) (guard : d325273 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 250 with
  | false =>
    have hg : d325272 p = 1 := by simpa only [d325273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41173 p hg
    simpa only [d325273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41175 (p : Pattern) (guard : d325274 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 249 with
  | false =>
    have hg : d325273 p = 1 := by simpa only [d325274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41174 p hg
    simpa only [d325274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41176 (p : Pattern) (guard : d325275 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 245 with
  | false =>
    have hg : d325274 p = 1 := by simpa only [d325275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41175 p hg
    simpa only [d325275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41177 (p : Pattern) (guard : d325276 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 200 with
  | false =>
    have hg : d325275 p = 1 := by simpa only [d325276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41176 p hg
    simpa only [d325276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41178 (p : Pattern) (guard : d325277 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 199 with
  | false =>
    have hg : d325276 p = 1 := by simpa only [d325277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41177 p hg
    simpa only [d325277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41179 (p : Pattern) (guard : d325278 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 186 with
  | false =>
    have hg : d325277 p = 1 := by simpa only [d325278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41178 p hg
    simpa only [d325278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41180 (p : Pattern) (guard : d325279 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 185 with
  | false =>
    have hg : d325278 p = 1 := by simpa only [d325279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41179 p hg
    simpa only [d325279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41181 (p : Pattern) (guard : d325280 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 184 with
  | false =>
    have hg : d325279 p = 1 := by simpa only [d325280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41180 p hg
    simpa only [d325280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41182 (p : Pattern) (guard : d325281 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 181 with
  | false =>
    have hg : d325280 p = 1 := by simpa only [d325281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41181 p hg
    simpa only [d325281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41183 (p : Pattern) (guard : d325282 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 177 with
  | false =>
    have hg : d325281 p = 1 := by simpa only [d325282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41182 p hg
    simpa only [d325282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41184 (p : Pattern) (guard : d325283 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 164 with
  | false =>
    have hg : d325282 p = 1 := by simpa only [d325283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41183 p hg
    simpa only [d325283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41185 (p : Pattern) (guard : d325284 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 156 with
  | false =>
    have hg : d325283 p = 1 := by simpa only [d325284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41184 p hg
    simpa only [d325284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41186 (p : Pattern) (guard : d325285 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 155 with
  | false =>
    have hg : d325284 p = 1 := by simpa only [d325285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41185 p hg
    simpa only [d325285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41187 (p : Pattern) (guard : d325286 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 134 with
  | false =>
    have hg : d325285 p = 1 := by simpa only [d325286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41186 p hg
    simpa only [d325286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41188 (p : Pattern) (guard : d325287 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 133 with
  | false =>
    have hg : d325286 p = 1 := by simpa only [d325287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41187 p hg
    simpa only [d325287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41189 (p : Pattern) (guard : d325288 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 120 with
  | false =>
    have hg : d325287 p = 1 := by simpa only [d325288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41188 p hg
    simpa only [d325288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41190 (p : Pattern) (guard : d325289 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 118 with
  | false =>
    have hg : d325288 p = 1 := by simpa only [d325289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41189 p hg
    simpa only [d325289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41191 (p : Pattern) (guard : d325290 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 114 with
  | false =>
    have hg : d325289 p = 1 := by simpa only [d325290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41190 p hg
    simpa only [d325290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41192 (p : Pattern) (guard : d325291 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 111 with
  | false =>
    have hg : d325290 p = 1 := by simpa only [d325291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41191 p hg
    simpa only [d325291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41193 (p : Pattern) (guard : d325292 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 98 with
  | false =>
    have hg : d325291 p = 1 := by simpa only [d325292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41192 p hg
    simpa only [d325292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41194 (p : Pattern) (guard : d325293 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 97 with
  | false =>
    have hg : d325292 p = 1 := by simpa only [d325293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41193 p hg
    simpa only [d325293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41195 (p : Pattern) (guard : d325294 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 94 with
  | false =>
    have hg : d325293 p = 1 := by simpa only [d325294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41194 p hg
    simpa only [d325294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41196 (p : Pattern) (guard : d325295 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 76 with
  | false =>
    have hg : d325294 p = 1 := by simpa only [d325295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41195 p hg
    simpa only [d325295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41197 (p : Pattern) (guard : d325296 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 67 with
  | false =>
    have hg : d325295 p = 1 := by simpa only [d325296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41196 p hg
    simpa only [d325296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41198 (p : Pattern) (guard : d325297 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 52 with
  | false =>
    have hg : d325296 p = 1 := by simpa only [d325297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41197 p hg
    simpa only [d325297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41199 (p : Pattern) (guard : d325298 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 47 with
  | false =>
    have hg : d325297 p = 1 := by simpa only [d325298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41198 p hg
    simpa only [d325298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41200 (p : Pattern) (guard : d325299 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 46 with
  | false =>
    have hg : d325298 p = 1 := by simpa only [d325299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41199 p hg
    simpa only [d325299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41201 (p : Pattern) (guard : d325300 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 45 with
  | false =>
    have hg : d325299 p = 1 := by simpa only [d325300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41200 p hg
    simpa only [d325300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41202 (p : Pattern) (guard : d325301 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 30 with
  | false =>
    have hg : d325300 p = 1 := by simpa only [d325301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41201 p hg
    simpa only [d325301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41203 (p : Pattern) (guard : d325302 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 29 with
  | false =>
    have hg : d325301 p = 1 := by simpa only [d325302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41202 p hg
    simpa only [d325302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41204 (p : Pattern) (guard : d325303 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 28 with
  | false =>
    have hg : d325302 p = 1 := by simpa only [d325303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41203 p hg
    simpa only [d325303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41205 (p : Pattern) (guard : d325304 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 27 with
  | false =>
    have hg : d325303 p = 1 := by simpa only [d325304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41204 p hg
    simpa only [d325304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41206 (p : Pattern) (guard : d325305 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 25 with
  | false =>
    have hg : d325304 p = 1 := by simpa only [d325305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41205 p hg
    simpa only [d325305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41207 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (-1 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41208 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (-2 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41209 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (-1 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41210 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (-2 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41211 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (1 : Int) + d326947 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41212 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (0 : Int) + d326947 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41213 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (-1 : Int) + d51635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41214 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (-2 : Int) + d51635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41215 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d338883 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41216 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d338883 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41217 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-1 : Int) + d50101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41218 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-2 : Int) + d50101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41219 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41220 (p : Pattern) (guard : d0 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41221 (p : Pattern) (guard : d0 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41222 (p : Pattern) (guard : d0 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41223 (p : Pattern) (guard : d0 p = 1) : d50949 p ≤ (1 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41224 (p : Pattern) (guard : d0 p = 1) : d50951 p ≤ (1 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41225 (p : Pattern) (guard : d0 p = 1) : d50904 p ≤ (1 : Int) + d47681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41226 (p : Pattern) (guard : d0 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41227 (p : Pattern) (guard : d0 p = 1) : d50906 p ≤ (1 : Int) + d47655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41228 (p : Pattern) (guard : d0 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41229 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (1 : Int) + d4 p := by
  omega
theorem compare41230 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41231 (p : Pattern) (guard : d15 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41229 p hg
    simpa only [d15, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41230 p hg
    simpa only [d15, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41232 (p : Pattern) (guard : d16 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41231 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41233 (p : Pattern) (guard : d17 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41232 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41234 (p : Pattern) (guard : d38813 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41233 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41235 (p : Pattern) (guard : d258091 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38813 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41234 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41236 (p : Pattern) (guard : d337158 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258091 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41235 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41237 (p : Pattern) (guard : d337173 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337158 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41236 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41238 (p : Pattern) (guard : d257183 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41234 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41239 (p : Pattern) (guard : d257184 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41238 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41240 (p : Pattern) (guard : d257185 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41239 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41241 (p : Pattern) (guard : d348400 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337173 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41237 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41240 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41242 (p : Pattern) (guard : d0 p = 1) : d50839 p ≤ (1 : Int) + d47618 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41243 (p : Pattern) (guard : d348401 p = 1) : d50840 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348400 p = 1 := by simpa only [d348401, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41241 p hg
    simpa only [d348401, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348401, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41242 p hg
    simpa only [d348401, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41244 (p : Pattern) (guard : d0 p = 1) : d50840 p ≤ (1 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41245 (p : Pattern) (guard : d348402 p = 1) : d50840 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348401 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41243 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41244 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41246 (p : Pattern) (guard : d0 p = 1) : d50880 p ≤ (1 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41247 (p : Pattern) (guard : d348403 p = 1) : d50881 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348402 p = 1 := by simpa only [d348403, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41245 p hg
    simpa only [d348403, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348403, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41246 p hg
    simpa only [d348403, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41248 (p : Pattern) (guard : d0 p = 1) : d50883 p ≤ (1 : Int) + d47662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41249 (p : Pattern) (guard : d348404 p = 1) : d50884 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348403 p = 1 := by simpa only [d348404, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41247 p hg
    simpa only [d348404, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348404, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41248 p hg
    simpa only [d348404, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
