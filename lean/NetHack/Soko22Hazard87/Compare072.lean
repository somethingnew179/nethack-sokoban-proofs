import NetHack.Soko22Hazard87.Compare071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18000 (p : Pattern) (guard : d113 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d112 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17999 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18001 (p : Pattern) (guard : d114 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d106 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17989 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d113 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18000 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18002 (p : Pattern) (guard : d115 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d40 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17897 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18003 (p : Pattern) (guard : d116 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d115 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18002 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18004 (p : Pattern) (guard : d117 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d116 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18003 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18005 (p : Pattern) (guard : d118 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d117 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18004 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18006 (p : Pattern) (guard : d119 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d118 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18005 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18007 (p : Pattern) (guard : d120 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d119 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18006 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18008 (p : Pattern) (guard : d121 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18009 (p : Pattern) (guard : d122 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d121 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18008 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18010 (p : Pattern) (guard : d123 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d122 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18009 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18011 (p : Pattern) (guard : d124 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d123 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18010 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18012 (p : Pattern) (guard : d125 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d124 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18011 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18013 (p : Pattern) (guard : d126 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d125 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18012 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18014 (p : Pattern) (guard : d138 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18015 (p : Pattern) (guard : d139 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18014 p hg
    simpa only [d139, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d139, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18016 (p : Pattern) (guard : d140 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18015 p hg
    simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18017 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d141, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18016 p hg
    simpa only [d141, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18018 (p : Pattern) (guard : d142 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18017 p hg
    simpa only [d142, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d142, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18019 (p : Pattern) (guard : d143 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18018 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17882 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18020 (p : Pattern) (guard : d144 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18019 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17884 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18021 (p : Pattern) (guard : d145 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18020 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17885 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18022 (p : Pattern) (guard : d146 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d146, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18021 p hg
    simpa only [d146, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18023 (p : Pattern) (guard : d147 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d147, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18022 p hg
    simpa only [d147, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18024 (p : Pattern) (guard : d148 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18023 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17888 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18025 (p : Pattern) (guard : d149 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18024 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17890 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18026 (p : Pattern) (guard : d150 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18025 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18027 (p : Pattern) (guard : d151 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18026 p hg
    simpa only [d151, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d151, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18028 (p : Pattern) (guard : d152 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d152, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18027 p hg
    simpa only [d152, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18029 (p : Pattern) (guard : d153 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17895 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18030 (p : Pattern) (guard : d154 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18029 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18031 (p : Pattern) (guard : d155 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18030 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18032 (p : Pattern) (guard : d156 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18031 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18033 (p : Pattern) (guard : d157 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18032 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17899 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18034 (p : Pattern) (guard : d4335 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d157 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18033 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18035 (p : Pattern) (guard : d4336 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4335 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18034 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17901 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18036 (p : Pattern) (guard : d51641 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d126 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18013 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4336 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18035 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18037 (p : Pattern) (guard : d51642 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d120 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18007 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51641 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18036 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18038 (p : Pattern) (guard : d51643 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51643, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d51643, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51642 p = 1 := by simpa only [d51643, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18037 p hg
    simpa only [d51643, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18039 (p : Pattern) (guard : d115 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d40 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17916 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18040 (p : Pattern) (guard : d116 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d115 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18039 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18041 (p : Pattern) (guard : d117 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d116 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18040 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18042 (p : Pattern) (guard : d118 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d117 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18041 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18043 (p : Pattern) (guard : d119 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d118 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18042 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18044 (p : Pattern) (guard : d120 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d119 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18043 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18045 (p : Pattern) (guard : d121 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17915 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18046 (p : Pattern) (guard : d122 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d121 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18045 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18047 (p : Pattern) (guard : d123 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d122 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18046 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18048 (p : Pattern) (guard : d124 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d123 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18047 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18049 (p : Pattern) (guard : d125 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d124 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18048 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18050 (p : Pattern) (guard : d126 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d125 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18049 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18051 (p : Pattern) (guard : d147 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d147, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18022 p hg
    simpa only [d147, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18052 (p : Pattern) (guard : d148 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18051 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17908 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18053 (p : Pattern) (guard : d149 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18052 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17910 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18054 (p : Pattern) (guard : d150 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18053 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18055 (p : Pattern) (guard : d151 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18054 p hg
    simpa only [d151, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d151, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18056 (p : Pattern) (guard : d152 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d152, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18055 p hg
    simpa only [d152, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18057 (p : Pattern) (guard : d153 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18056 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17914 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18058 (p : Pattern) (guard : d154 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18057 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18059 (p : Pattern) (guard : d155 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18058 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18060 (p : Pattern) (guard : d156 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18059 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18061 (p : Pattern) (guard : d157 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18060 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17918 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18062 (p : Pattern) (guard : d4335 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d157 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18061 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18063 (p : Pattern) (guard : d4336 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4335 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18062 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17920 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18064 (p : Pattern) (guard : d51641 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d126 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18050 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4336 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18063 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18065 (p : Pattern) (guard : d51642 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d120 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18044 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51641 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18064 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18066 (p : Pattern) (guard : d194 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d115 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18002 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18067 (p : Pattern) (guard : d195 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d194 p = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18066 p hg
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18068 (p : Pattern) (guard : d196 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d195 p = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18067 p hg
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18069 (p : Pattern) (guard : d197 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d196 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18068 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18070 (p : Pattern) (guard : d198 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d197 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18069 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18071 (p : Pattern) (guard : d199 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d122 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18009 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18072 (p : Pattern) (guard : d200 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d199 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18071 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18073 (p : Pattern) (guard : d201 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d200 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18072 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18074 (p : Pattern) (guard : d202 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d201 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18073 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18075 (p : Pattern) (guard : d203 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18031 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18076 (p : Pattern) (guard : d204 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18075 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17924 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18077 (p : Pattern) (guard : d4340 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d204 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18076 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18078 (p : Pattern) (guard : d4341 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4340 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18077 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17926 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18079 (p : Pattern) (guard : d51644 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d202 p = 1 := by simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18074 p hg
    simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4341 p = 1 := by simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18078 p hg
    simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18080 (p : Pattern) (guard : d51645 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d198 p = 1 := by simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18070 p hg
    simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51644 p = 1 := by simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18079 p hg
    simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18081 (p : Pattern) (guard : d51646 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51642 p = 1 := by simpa only [d51646, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18065 p hg
    simpa only [d51646, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51645 p = 1 := by simpa only [d51646, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18080 p hg
    simpa only [d51646, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18082 (p : Pattern) (guard : d51647 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51643 p = 1 := by simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18038 p hg
    simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51646 p = 1 := by simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18081 p hg
    simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18083 (p : Pattern) (guard : d213 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d213, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17993 p hg
    simpa only [d213, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d213, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d213, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18084 (p : Pattern) (guard : d214 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d213 p = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18083 p hg
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18085 (p : Pattern) (guard : d51648 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51647 p = 1 := by simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18082 p hg
    simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d214 p = 1 := by simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18084 p hg
    simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18086 (p : Pattern) (guard : d51649 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51648 p = 1 := by simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18085 p hg
    simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18087 (p : Pattern) (guard : d51650 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d114 p = 1 := by simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18001 p hg
    simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51649 p = 1 := by simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18086 p hg
    simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18088 (p : Pattern) (guard : d138 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18089 (p : Pattern) (guard : d139 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18088 p hg
    simpa only [d139, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d139, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18090 (p : Pattern) (guard : d140 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18089 p hg
    simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18091 (p : Pattern) (guard : d141 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18090 p hg
    simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18092 (p : Pattern) (guard : d142 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18091 p hg
    simpa only [d142, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d142, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18093 (p : Pattern) (guard : d143 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18092 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17948 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18094 (p : Pattern) (guard : d144 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18093 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17950 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18095 (p : Pattern) (guard : d145 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18094 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17951 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18096 (p : Pattern) (guard : d146 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d146, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18095 p hg
    simpa only [d146, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18097 (p : Pattern) (guard : d147 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d147, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18096 p hg
    simpa only [d147, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18098 (p : Pattern) (guard : d148 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18097 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17954 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18099 (p : Pattern) (guard : d149 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18098 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17956 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18100 (p : Pattern) (guard : d150 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18099 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18101 (p : Pattern) (guard : d151 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18100 p hg
    simpa only [d151, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d151, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18102 (p : Pattern) (guard : d152 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18101 p hg
    simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18103 (p : Pattern) (guard : d153 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18102 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17961 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18104 (p : Pattern) (guard : d154 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18103 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18105 (p : Pattern) (guard : d155 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18104 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18106 (p : Pattern) (guard : d203 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18105 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18107 (p : Pattern) (guard : d204 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18106 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17965 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18108 (p : Pattern) (guard : d4340 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d204 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18107 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18109 (p : Pattern) (guard : d4341 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4340 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18108 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17967 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18110 (p : Pattern) (guard : d4342 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4341 p = 1 := by simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18109 p hg
    simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18111 (p : Pattern) (guard : d4343 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4342 p = 1 := by simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18110 p hg
    simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18112 (p : Pattern) (guard : d4349 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4349, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d4349, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4343 p = 1 := by simpa only [d4349, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18111 p hg
    simpa only [d4349, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18113 (p : Pattern) (guard : d4350 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4349 p = 1 := by simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18112 p hg
    simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18114 (p : Pattern) (guard : d4351 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d4350 p = 1 := by simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18113 p hg
    simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18115 (p : Pattern) (guard : d4352 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d4351 p = 1 := by simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18114 p hg
    simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18116 (p : Pattern) (guard : d4353 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d4352 p = 1 := by simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18115 p hg
    simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18117 (p : Pattern) (guard : d51651 p = 1) : d48359 p ≤ (1 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d51650 p = 1 := by simpa only [d51651, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18087 p hg
    simpa only [d51651, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4353 p = 1 := by simpa only [d51651, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18116 p hg
    simpa only [d51651, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18118 (p : Pattern) (guard : d54298 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d51651 p = 1 := by simpa only [d54298, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d54298, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54298, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d54298, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18119 (p : Pattern) (guard : d54299 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d54299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54298 p = 1 := by simpa only [d54299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18118 p hg
    simpa only [d54299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18120 (p : Pattern) (guard : d54300 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d54300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54299 p = 1 := by simpa only [d54300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18119 p hg
    simpa only [d54300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18121 (p : Pattern) (guard : d54301 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d54301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54300 p = 1 := by simpa only [d54301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18120 p hg
    simpa only [d54301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18122 (p : Pattern) (guard : d54302 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d54302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54301 p = 1 := by simpa only [d54302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18121 p hg
    simpa only [d54302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18123 (p : Pattern) (guard : d54303 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d2676 p = 1 := by simpa only [d54303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17982 p hg
    simpa only [d54303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54302 p = 1 := by simpa only [d54303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18122 p hg
    simpa only [d54303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18124 (p : Pattern) (guard : d280 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18033 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18125 (p : Pattern) (guard : d281 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18124 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18126 (p : Pattern) (guard : d282 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18125 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18127 (p : Pattern) (guard : d283 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18126 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18128 (p : Pattern) (guard : d284 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d283 p = 1 := by simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18127 p hg
    simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18129 (p : Pattern) (guard : d285 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d284 p = 1 := by simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18128 p hg
    simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18130 (p : Pattern) (guard : d286 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285 p = 1 := by simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18129 p hg
    simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18131 (p : Pattern) (guard : d280 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18061 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18132 (p : Pattern) (guard : d281 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18131 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18133 (p : Pattern) (guard : d282 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18132 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18134 (p : Pattern) (guard : d283 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18133 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18135 (p : Pattern) (guard : d287 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d204 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18076 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18136 (p : Pattern) (guard : d288 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18135 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18137 (p : Pattern) (guard : d289 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d288 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18136 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18138 (p : Pattern) (guard : d290 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d289 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18137 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18139 (p : Pattern) (guard : d291 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18134 p hg
    simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d290 p = 1 := by simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18138 p hg
    simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18140 (p : Pattern) (guard : d292 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d284 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18128 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d291 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18139 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18141 (p : Pattern) (guard : d293 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d292 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18140 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18142 (p : Pattern) (guard : d294 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d286 p = 1 := by simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18130 p hg
    simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293 p = 1 := by simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18141 p hg
    simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18143 (p : Pattern) (guard : d295 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d154 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18030 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18144 (p : Pattern) (guard : d296 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18143 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18145 (p : Pattern) (guard : d297 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d296 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18144 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d116 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18003 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18146 (p : Pattern) (guard : d298 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d297 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18145 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18147 (p : Pattern) (guard : d299 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d298 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18146 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18148 (p : Pattern) (guard : d300 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d299 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18147 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18149 (p : Pattern) (guard : d301 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d153 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18029 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18150 (p : Pattern) (guard : d302 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d301 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18149 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18151 (p : Pattern) (guard : d303 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d302 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18150 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18152 (p : Pattern) (guard : d304 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d303 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18151 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d123 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18010 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18153 (p : Pattern) (guard : d305 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d304 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18152 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18154 (p : Pattern) (guard : d306 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d305 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18153 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18155 (p : Pattern) (guard : d318 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18156 (p : Pattern) (guard : d319 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18155 p hg
    simpa only [d319, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d319, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18157 (p : Pattern) (guard : d320 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18156 p hg
    simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18158 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d321, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18157 p hg
    simpa only [d321, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18159 (p : Pattern) (guard : d322 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18158 p hg
    simpa only [d322, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d322, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18160 (p : Pattern) (guard : d323 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18159 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18018 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18161 (p : Pattern) (guard : d9381 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18162 (p : Pattern) (guard : d9382 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9381 p = 1 := by simpa only [d9382, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18161 p hg
    simpa only [d9382, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9382, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9382, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18163 (p : Pattern) (guard : d9384 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9382 p = 1 := by simpa only [d9384, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18162 p hg
    simpa only [d9384, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9384, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9384, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18164 (p : Pattern) (guard : d12493 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12493, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d12493, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9384 p = 1 := by simpa only [d12493, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18163 p hg
    simpa only [d12493, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18165 (p : Pattern) (guard : d12494 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18164 p hg
    simpa only [d12494, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d12494, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18166 (p : Pattern) (guard : d12495 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18165 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17882 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18167 (p : Pattern) (guard : d15966 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18160 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18166 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18168 (p : Pattern) (guard : d15967 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18167 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18020 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18169 (p : Pattern) (guard : d15968 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d15968, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18168 p hg
    simpa only [d15968, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18170 (p : Pattern) (guard : d15969 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d15969, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18169 p hg
    simpa only [d15969, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18171 (p : Pattern) (guard : d15970 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18170 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18023 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18172 (p : Pattern) (guard : d15971 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18171 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18024 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18173 (p : Pattern) (guard : d15972 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d15971 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18172 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18174 (p : Pattern) (guard : d15973 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d15972 p = 1 := by simpa only [d15973, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18173 p hg
    simpa only [d15973, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15973, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d15973, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18175 (p : Pattern) (guard : d15974 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15974, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d15974, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15973 p = 1 := by simpa only [d15974, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18174 p hg
    simpa only [d15974, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18176 (p : Pattern) (guard : d15975 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d15974 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18175 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d152 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18177 (p : Pattern) (guard : d15976 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d15975 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18176 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18178 (p : Pattern) (guard : d15977 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d15976 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18177 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18179 (p : Pattern) (guard : d15978 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15977 p = 1 := by simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18178 p hg
    simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18180 (p : Pattern) (guard : d15979 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d15978 p = 1 := by simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18179 p hg
    simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d156 p = 1 := by simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18032 p hg
    simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18181 (p : Pattern) (guard : d128191 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d15979 p = 1 := by simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18180 p hg
    simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18182 (p : Pattern) (guard : d4733 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18183 (p : Pattern) (guard : d4734 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d4733 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18182 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18184 (p : Pattern) (guard : d4735 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d4734 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18183 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18185 (p : Pattern) (guard : d4736 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4735 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18184 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18186 (p : Pattern) (guard : d4737 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d4736 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18185 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18187 (p : Pattern) (guard : d5350 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d4737 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18186 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18188 (p : Pattern) (guard : d128192 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128191 p = 1 := by simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18181 p hg
    simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5350 p = 1 := by simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18187 p hg
    simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18189 (p : Pattern) (guard : d128193 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d306 p = 1 := by simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18154 p hg
    simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128192 p = 1 := by simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18188 p hg
    simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18190 (p : Pattern) (guard : d128194 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d300 p = 1 := by simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18148 p hg
    simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128193 p = 1 := by simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18189 p hg
    simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18191 (p : Pattern) (guard : d128195 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128195, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128195, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128194 p = 1 := by simpa only [d128195, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18190 p hg
    simpa only [d128195, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18192 (p : Pattern) (guard : d295 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d154 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18058 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18193 (p : Pattern) (guard : d296 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18192 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18194 (p : Pattern) (guard : d297 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d296 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18193 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d116 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18040 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18195 (p : Pattern) (guard : d298 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d297 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18194 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18196 (p : Pattern) (guard : d299 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d298 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18195 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18197 (p : Pattern) (guard : d300 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d299 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18196 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18198 (p : Pattern) (guard : d301 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d153 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18057 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18199 (p : Pattern) (guard : d302 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d301 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18198 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18200 (p : Pattern) (guard : d303 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d302 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18199 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18201 (p : Pattern) (guard : d304 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d303 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18200 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d123 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18047 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18202 (p : Pattern) (guard : d305 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d304 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18201 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18203 (p : Pattern) (guard : d306 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d305 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18202 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18204 (p : Pattern) (guard : d15969 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d15969, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18169 p hg
    simpa only [d15969, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18205 (p : Pattern) (guard : d15970 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18204 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18051 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18206 (p : Pattern) (guard : d15971 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18205 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18052 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18207 (p : Pattern) (guard : d15972 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d15971 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18206 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18208 (p : Pattern) (guard : d15973 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d15972 p = 1 := by simpa only [d15973, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18207 p hg
    simpa only [d15973, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15973, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d15973, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18209 (p : Pattern) (guard : d15974 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15974, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d15974, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15973 p = 1 := by simpa only [d15974, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18208 p hg
    simpa only [d15974, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18210 (p : Pattern) (guard : d15975 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d15974 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18209 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d152 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18056 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18211 (p : Pattern) (guard : d15976 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d15975 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18210 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18212 (p : Pattern) (guard : d15977 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d15976 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18211 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18213 (p : Pattern) (guard : d15978 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15977 p = 1 := by simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18212 p hg
    simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18214 (p : Pattern) (guard : d15979 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d15978 p = 1 := by simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18213 p hg
    simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d156 p = 1 := by simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18060 p hg
    simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18215 (p : Pattern) (guard : d128191 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d15979 p = 1 := by simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18214 p hg
    simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18216 (p : Pattern) (guard : d4733 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18056 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18217 (p : Pattern) (guard : d4734 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d4733 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18216 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18218 (p : Pattern) (guard : d4735 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d4734 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18217 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18219 (p : Pattern) (guard : d4736 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4735 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18218 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18220 (p : Pattern) (guard : d4737 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d4736 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18219 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18221 (p : Pattern) (guard : d5350 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d4737 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18220 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18222 (p : Pattern) (guard : d128192 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128191 p = 1 := by simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18215 p hg
    simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5350 p = 1 := by simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18221 p hg
    simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18223 (p : Pattern) (guard : d128193 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d306 p = 1 := by simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18203 p hg
    simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128192 p = 1 := by simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18222 p hg
    simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18224 (p : Pattern) (guard : d128194 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d300 p = 1 := by simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18197 p hg
    simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128193 p = 1 := by simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18223 p hg
    simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18225 (p : Pattern) (guard : d376 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295 p = 1 := by simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18143 p hg
    simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18226 (p : Pattern) (guard : d377 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d376 p = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18225 p hg
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d194 p = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18066 p hg
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18227 (p : Pattern) (guard : d378 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d377 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18226 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18228 (p : Pattern) (guard : d379 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d378 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18227 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18229 (p : Pattern) (guard : d380 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d379 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18228 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18230 (p : Pattern) (guard : d381 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d302 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18150 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18231 (p : Pattern) (guard : d382 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d381 p = 1 := by simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18230 p hg
    simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d199 p = 1 := by simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18071 p hg
    simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18232 (p : Pattern) (guard : d383 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d382 p = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18231 p hg
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18233 (p : Pattern) (guard : d384 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d383 p = 1 := by simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18232 p hg
    simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18234 (p : Pattern) (guard : d15985 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d15977 p = 1 := by simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18178 p hg
    simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18235 (p : Pattern) (guard : d15986 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d15985 p = 1 := by simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18234 p hg
    simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d203 p = 1 := by simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18075 p hg
    simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18236 (p : Pattern) (guard : d128196 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d15986 p = 1 := by simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18235 p hg
    simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18237 (p : Pattern) (guard : d5355 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d4735 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18184 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18238 (p : Pattern) (guard : d5356 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5355 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18237 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18239 (p : Pattern) (guard : d5357 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5356 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18238 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18240 (p : Pattern) (guard : d128197 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128196 p = 1 := by simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18236 p hg
    simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5357 p = 1 := by simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18239 p hg
    simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18241 (p : Pattern) (guard : d128198 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d384 p = 1 := by simpa only [d128198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18233 p hg
    simpa only [d128198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128197 p = 1 := by simpa only [d128198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18240 p hg
    simpa only [d128198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18242 (p : Pattern) (guard : d128199 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d380 p = 1 := by simpa only [d128199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18229 p hg
    simpa only [d128199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128198 p = 1 := by simpa only [d128199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18241 p hg
    simpa only [d128199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18243 (p : Pattern) (guard : d128200 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128194 p = 1 := by simpa only [d128200, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18224 p hg
    simpa only [d128200, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128199 p = 1 := by simpa only [d128200, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18242 p hg
    simpa only [d128200, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18244 (p : Pattern) (guard : d128201 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128195 p = 1 := by simpa only [d128201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18191 p hg
    simpa only [d128201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128200 p = 1 := by simpa only [d128201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18243 p hg
    simpa only [d128201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18245 (p : Pattern) (guard : d397 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d397, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18134 p hg
    simpa only [d397, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d397, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17986 p hg
    simpa only [d397, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18246 (p : Pattern) (guard : d398 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d397 p = 1 := by simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18245 p hg
    simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17998 p hg
    simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18247 (p : Pattern) (guard : d128202 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128201 p = 1 := by simpa only [d128202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18244 p hg
    simpa only [d128202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d398 p = 1 := by simpa only [d128202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18246 p hg
    simpa only [d128202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18248 (p : Pattern) (guard : d128203 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128202 p = 1 := by simpa only [d128203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18247 p hg
    simpa only [d128203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d128203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18249 (p : Pattern) (guard : d128204 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294 p = 1 := by simpa only [d128204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18142 p hg
    simpa only [d128204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128203 p = 1 := by simpa only [d128204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18248 p hg
    simpa only [d128204, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
