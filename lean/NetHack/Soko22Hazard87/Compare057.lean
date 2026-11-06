import NetHack.Soko22Hazard87.Compare056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14250 (p : Pattern) (guard : d16072 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16071 p = 1 := by simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14249 p hg
    simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14251 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14252 (p : Pattern) (guard : d546 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14251 p hg
    simpa only [d546, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d546, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14253 (p : Pattern) (guard : d16073 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14254 (p : Pattern) (guard : d16074 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14253 p hg
    simpa only [d16074, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d16074, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14255 (p : Pattern) (guard : d16075 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14252 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14254 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14256 (p : Pattern) (guard : d12748 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14257 (p : Pattern) (guard : d12749 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14256 p hg
    simpa only [d12749, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d12749, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14258 (p : Pattern) (guard : d16076 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14257 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12494 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14000 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14259 (p : Pattern) (guard : d16077 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14255 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16076 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14258 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14260 (p : Pattern) (guard : d16078 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16077 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14259 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15966 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14002 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14261 (p : Pattern) (guard : d16079 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16079, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16079, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16078 p = 1 := by simpa only [d16079, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14260 p hg
    simpa only [d16079, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14262 (p : Pattern) (guard : d16080 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16080, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16080, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16079 p = 1 := by simpa only [d16080, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14261 p hg
    simpa only [d16080, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14263 (p : Pattern) (guard : d16081 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12495 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14001 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13675 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14264 (p : Pattern) (guard : d16082 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14002 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16081 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14263 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14265 (p : Pattern) (guard : d16083 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16083, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16083, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16082 p = 1 := by simpa only [d16083, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14264 p hg
    simpa only [d16083, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14266 (p : Pattern) (guard : d16084 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16084, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16084, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16083 p = 1 := by simpa only [d16084, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14265 p hg
    simpa only [d16084, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14267 (p : Pattern) (guard : d16085 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16080 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14262 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16084 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14266 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14268 (p : Pattern) (guard : d16086 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16085 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14267 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15970 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14006 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14269 (p : Pattern) (guard : d16087 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16086 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14268 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14270 (p : Pattern) (guard : d16088 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16087 p = 1 := by simpa only [d16088, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14269 p hg
    simpa only [d16088, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16088, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16088, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14271 (p : Pattern) (guard : d16089 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16089, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16089, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16088 p = 1 := by simpa only [d16089, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14270 p hg
    simpa only [d16089, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14272 (p : Pattern) (guard : d16090 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16089 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14271 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16038 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14180 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14273 (p : Pattern) (guard : d16091 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16090 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14272 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14274 (p : Pattern) (guard : d16092 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16091 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14273 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14275 (p : Pattern) (guard : d16093 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16092 p = 1 := by simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14274 p hg
    simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14276 (p : Pattern) (guard : d16094 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16093 p = 1 := by simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14275 p hg
    simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16042 p = 1 := by simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14188 p hg
    simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14277 (p : Pattern) (guard : d128230 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16094 p = 1 := by simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14276 p hg
    simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14278 (p : Pattern) (guard : d16111 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14180 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14279 (p : Pattern) (guard : d16112 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16111 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14278 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14280 (p : Pattern) (guard : d16113 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16112 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14279 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14281 (p : Pattern) (guard : d16114 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16113 p = 1 := by simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14280 p hg
    simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14282 (p : Pattern) (guard : d16115 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16114 p = 1 := by simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14281 p hg
    simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14283 (p : Pattern) (guard : d16116 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16115 p = 1 := by simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14282 p hg
    simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14284 (p : Pattern) (guard : d128231 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128230 p = 1 := by simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14277 p hg
    simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16116 p = 1 := by simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14283 p hg
    simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14285 (p : Pattern) (guard : d128232 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16072 p = 1 := by simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14250 p hg
    simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128231 p = 1 := by simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14284 p hg
    simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14286 (p : Pattern) (guard : d128233 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16066 p = 1 := by simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14241 p hg
    simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128232 p = 1 := by simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14285 p hg
    simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14287 (p : Pattern) (guard : d128234 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128234, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128234, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128233 p = 1 := by simpa only [d128234, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14286 p hg
    simpa only [d128234, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14288 (p : Pattern) (guard : d16061 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16040 p = 1 := by simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14211 p hg
    simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14289 (p : Pattern) (guard : d16062 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16061 p = 1 := by simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14288 p hg
    simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14290 (p : Pattern) (guard : d513 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d489 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14215 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14291 (p : Pattern) (guard : d514 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d513 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14290 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14292 (p : Pattern) (guard : d16063 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16062 p = 1 := by simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14289 p hg
    simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d514 p = 1 := by simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14291 p hg
    simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14293 (p : Pattern) (guard : d16064 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16063 p = 1 := by simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14292 p hg
    simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14294 (p : Pattern) (guard : d16065 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16064 p = 1 := by simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14293 p hg
    simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14295 (p : Pattern) (guard : d16066 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16065 p = 1 := by simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14294 p hg
    simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14296 (p : Pattern) (guard : d16067 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16039 p = 1 := by simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14210 p hg
    simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14297 (p : Pattern) (guard : d16068 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16067 p = 1 := by simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14296 p hg
    simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14298 (p : Pattern) (guard : d16069 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16068 p = 1 := by simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14297 p hg
    simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14299 (p : Pattern) (guard : d522 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d488 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14214 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14300 (p : Pattern) (guard : d523 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d522 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14299 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14301 (p : Pattern) (guard : d524 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d523 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14300 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14302 (p : Pattern) (guard : d16070 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16069 p = 1 := by simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14298 p hg
    simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d524 p = 1 := by simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14301 p hg
    simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14303 (p : Pattern) (guard : d16071 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16070 p = 1 := by simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14302 p hg
    simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14304 (p : Pattern) (guard : d16072 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16071 p = 1 := by simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14303 p hg
    simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14305 (p : Pattern) (guard : d16080 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16080, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16080, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16079 p = 1 := by simpa only [d16080, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14261 p hg
    simpa only [d16080, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14306 (p : Pattern) (guard : d16084 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16084, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16084, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16083 p = 1 := by simpa only [d16084, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14265 p hg
    simpa only [d16084, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14307 (p : Pattern) (guard : d16085 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16080 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14305 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16084 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14306 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14308 (p : Pattern) (guard : d16086 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16085 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14307 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15970 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14040 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14309 (p : Pattern) (guard : d16087 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16086 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14308 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14310 (p : Pattern) (guard : d16088 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16087 p = 1 := by simpa only [d16088, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14309 p hg
    simpa only [d16088, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16088, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16088, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14311 (p : Pattern) (guard : d16089 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16089, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16089, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16088 p = 1 := by simpa only [d16089, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14310 p hg
    simpa only [d16089, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14312 (p : Pattern) (guard : d16090 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16089 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14311 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16038 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14313 (p : Pattern) (guard : d16091 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16090 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14312 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14314 (p : Pattern) (guard : d16092 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16091 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14313 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14315 (p : Pattern) (guard : d16093 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16092 p = 1 := by simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14314 p hg
    simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14316 (p : Pattern) (guard : d16094 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16093 p = 1 := by simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14315 p hg
    simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16042 p = 1 := by simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14213 p hg
    simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14317 (p : Pattern) (guard : d128230 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16094 p = 1 := by simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14316 p hg
    simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14318 (p : Pattern) (guard : d16111 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14319 (p : Pattern) (guard : d16112 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16111 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14318 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14320 (p : Pattern) (guard : d16113 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16112 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14319 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14321 (p : Pattern) (guard : d16114 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16113 p = 1 := by simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14320 p hg
    simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14322 (p : Pattern) (guard : d16115 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16114 p = 1 := by simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14321 p hg
    simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14323 (p : Pattern) (guard : d16116 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16115 p = 1 := by simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14322 p hg
    simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14324 (p : Pattern) (guard : d128231 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128230 p = 1 := by simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14317 p hg
    simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16116 p = 1 := by simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14323 p hg
    simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14325 (p : Pattern) (guard : d128232 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16072 p = 1 := by simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14304 p hg
    simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128231 p = 1 := by simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14324 p hg
    simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14326 (p : Pattern) (guard : d128233 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16066 p = 1 := by simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14295 p hg
    simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128232 p = 1 := by simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14325 p hg
    simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14327 (p : Pattern) (guard : d16121 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16061 p = 1 := by simpa only [d16121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14234 p hg
    simpa only [d16121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14328 (p : Pattern) (guard : d610 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d513 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14236 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14329 (p : Pattern) (guard : d16122 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16121 p = 1 := by simpa only [d16122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14327 p hg
    simpa only [d16122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d610 p = 1 := by simpa only [d16122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14328 p hg
    simpa only [d16122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14330 (p : Pattern) (guard : d16123 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16122 p = 1 := by simpa only [d16123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14329 p hg
    simpa only [d16123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14331 (p : Pattern) (guard : d16124 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16123 p = 1 := by simpa only [d16124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14330 p hg
    simpa only [d16124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14332 (p : Pattern) (guard : d16125 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16124 p = 1 := by simpa only [d16125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14331 p hg
    simpa only [d16125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14333 (p : Pattern) (guard : d16126 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16068 p = 1 := by simpa only [d16126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14243 p hg
    simpa only [d16126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14334 (p : Pattern) (guard : d616 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d523 p = 1 := by simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14246 p hg
    simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14335 (p : Pattern) (guard : d16127 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16126 p = 1 := by simpa only [d16127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14333 p hg
    simpa only [d16127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d616 p = 1 := by simpa only [d16127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14334 p hg
    simpa only [d16127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14336 (p : Pattern) (guard : d16128 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16127 p = 1 := by simpa only [d16128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14335 p hg
    simpa only [d16128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14337 (p : Pattern) (guard : d16129 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16128 p = 1 := by simpa only [d16129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14336 p hg
    simpa only [d16129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14338 (p : Pattern) (guard : d16130 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16092 p = 1 := by simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14274 p hg
    simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14339 (p : Pattern) (guard : d16131 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16130 p = 1 := by simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14338 p hg
    simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16051 p = 1 := by simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14223 p hg
    simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14340 (p : Pattern) (guard : d128235 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16131 p = 1 := by simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14339 p hg
    simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14341 (p : Pattern) (guard : d16135 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16113 p = 1 := by simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14280 p hg
    simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14342 (p : Pattern) (guard : d16136 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16135 p = 1 := by simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14341 p hg
    simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14343 (p : Pattern) (guard : d16137 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16136 p = 1 := by simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14344 (p : Pattern) (guard : d128236 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128235 p = 1 := by simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14340 p hg
    simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16137 p = 1 := by simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14343 p hg
    simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14345 (p : Pattern) (guard : d128237 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16129 p = 1 := by simpa only [d128237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14337 p hg
    simpa only [d128237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128236 p = 1 := by simpa only [d128237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14344 p hg
    simpa only [d128237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14346 (p : Pattern) (guard : d128238 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16125 p = 1 := by simpa only [d128238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14332 p hg
    simpa only [d128238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128237 p = 1 := by simpa only [d128238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14345 p hg
    simpa only [d128238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14347 (p : Pattern) (guard : d128239 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128233 p = 1 := by simpa only [d128239, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14326 p hg
    simpa only [d128239, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128238 p = 1 := by simpa only [d128239, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14346 p hg
    simpa only [d128239, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14348 (p : Pattern) (guard : d128240 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128234 p = 1 := by simpa only [d128240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14287 p hg
    simpa only [d128240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128239 p = 1 := by simpa only [d128240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14347 p hg
    simpa only [d128240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14349 (p : Pattern) (guard : d633 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d491 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14192 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14350 (p : Pattern) (guard : d634 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d633 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14349 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14351 (p : Pattern) (guard : d635 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d634 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14350 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14352 (p : Pattern) (guard : d636 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d635 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14351 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14353 (p : Pattern) (guard : d637 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d636 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14352 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14354 (p : Pattern) (guard : d16143 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16047 p = 1 := by simpa only [d16143, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14222 p hg
    simpa only [d16143, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d637 p = 1 := by simpa only [d16143, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14353 p hg
    simpa only [d16143, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14355 (p : Pattern) (guard : d633 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d491 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14217 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14356 (p : Pattern) (guard : d634 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d633 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14355 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14357 (p : Pattern) (guard : d635 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d634 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14356 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14358 (p : Pattern) (guard : d636 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d635 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14357 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14359 (p : Pattern) (guard : d637 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d636 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14358 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14360 (p : Pattern) (guard : d639 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d501 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14224 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14361 (p : Pattern) (guard : d640 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d639 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14360 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14362 (p : Pattern) (guard : d641 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d640 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14361 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14363 (p : Pattern) (guard : d642 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d641 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14362 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14364 (p : Pattern) (guard : d643 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d642 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14363 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14365 (p : Pattern) (guard : d644 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d637 p = 1 := by simpa only [d644, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14359 p hg
    simpa only [d644, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d643 p = 1 := by simpa only [d644, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14364 p hg
    simpa only [d644, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14366 (p : Pattern) (guard : d16144 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16143 p = 1 := by simpa only [d16144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14354 p hg
    simpa only [d16144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d644 p = 1 := by simpa only [d16144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14365 p hg
    simpa only [d16144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14367 (p : Pattern) (guard : d128241 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128240 p = 1 := by simpa only [d128241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14348 p hg
    simpa only [d128241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16144 p = 1 := by simpa only [d128241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14366 p hg
    simpa only [d128241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14368 (p : Pattern) (guard : d128242 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128241 p = 1 := by simpa only [d128242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14367 p hg
    simpa only [d128242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d128242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14369 (p : Pattern) (guard : d128243 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d16060 p = 1 := by simpa only [d128243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14233 p hg
    simpa only [d128243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128242 p = 1 := by simpa only [d128243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14368 p hg
    simpa only [d128243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14370 (p : Pattern) (guard : d545 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14371 (p : Pattern) (guard : d546 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14370 p hg
    simpa only [d546, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d546, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14372 (p : Pattern) (guard : d16073 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14373 (p : Pattern) (guard : d16074 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14372 p hg
    simpa only [d16074, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d16074, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14374 (p : Pattern) (guard : d16075 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14371 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14373 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14375 (p : Pattern) (guard : d12748 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14376 (p : Pattern) (guard : d12749 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14375 p hg
    simpa only [d12749, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d12749, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14377 (p : Pattern) (guard : d16076 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14376 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12494 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14089 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14378 (p : Pattern) (guard : d16077 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14374 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16076 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14377 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14379 (p : Pattern) (guard : d16078 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16077 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14378 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15966 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14091 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14380 (p : Pattern) (guard : d16079 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16079, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16079, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16078 p = 1 := by simpa only [d16079, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14379 p hg
    simpa only [d16079, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14381 (p : Pattern) (guard : d16080 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16080, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16080, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16079 p = 1 := by simpa only [d16080, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14380 p hg
    simpa only [d16080, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14382 (p : Pattern) (guard : d16081 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12495 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14090 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13735 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14383 (p : Pattern) (guard : d16082 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14091 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16081 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14382 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14384 (p : Pattern) (guard : d16083 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16083, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16083, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16082 p = 1 := by simpa only [d16083, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14383 p hg
    simpa only [d16083, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14385 (p : Pattern) (guard : d16084 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16084, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16084, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16083 p = 1 := by simpa only [d16084, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14384 p hg
    simpa only [d16084, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14386 (p : Pattern) (guard : d16085 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16080 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14381 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16084 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14385 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14387 (p : Pattern) (guard : d16086 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16085 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14386 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15970 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14095 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14388 (p : Pattern) (guard : d16087 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16086 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14387 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14389 (p : Pattern) (guard : d16088 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16087 p = 1 := by simpa only [d16088, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14388 p hg
    simpa only [d16088, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16088, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16088, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14390 (p : Pattern) (guard : d16089 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16089, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16089, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16088 p = 1 := by simpa only [d16089, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14389 p hg
    simpa only [d16089, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14391 (p : Pattern) (guard : d475 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13911 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14392 (p : Pattern) (guard : d16035 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14095 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14391 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14393 (p : Pattern) (guard : d16036 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14392 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14394 (p : Pattern) (guard : d16037 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14393 p hg
    simpa only [d16037, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16037, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14395 (p : Pattern) (guard : d16038 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14394 p hg
    simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14396 (p : Pattern) (guard : d16090 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16089 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14390 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16038 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14395 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14397 (p : Pattern) (guard : d16091 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16090 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14396 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14398 (p : Pattern) (guard : d16092 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16091 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14397 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14399 (p : Pattern) (guard : d16130 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16092 p = 1 := by simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14398 p hg
    simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14400 (p : Pattern) (guard : d480 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14391 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14401 (p : Pattern) (guard : d481 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14400 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14402 (p : Pattern) (guard : d482 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14401 p hg
    simpa only [d482, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d482, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14403 (p : Pattern) (guard : d483 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14402 p hg
    simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14404 (p : Pattern) (guard : d16039 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14395 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14403 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14405 (p : Pattern) (guard : d16040 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14404 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14406 (p : Pattern) (guard : d16041 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14405 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14407 (p : Pattern) (guard : d16051 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16041 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14406 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14408 (p : Pattern) (guard : d16131 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16130 p = 1 := by simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14399 p hg
    simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16051 p = 1 := by simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14407 p hg
    simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14409 (p : Pattern) (guard : d128235 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16131 p = 1 := by simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14408 p hg
    simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14410 (p : Pattern) (guard : d16111 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14395 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14411 (p : Pattern) (guard : d16112 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16111 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14410 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14412 (p : Pattern) (guard : d16113 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16112 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14411 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14413 (p : Pattern) (guard : d16135 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16113 p = 1 := by simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14412 p hg
    simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14414 (p : Pattern) (guard : d16136 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16135 p = 1 := by simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14413 p hg
    simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14415 (p : Pattern) (guard : d16137 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16136 p = 1 := by simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14414 p hg
    simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14416 (p : Pattern) (guard : d128236 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128235 p = 1 := by simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14409 p hg
    simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16137 p = 1 := by simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14415 p hg
    simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14417 (p : Pattern) (guard : d128244 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128236 p = 1 := by simpa only [d128244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14416 p hg
    simpa only [d128244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14418 (p : Pattern) (guard : d128245 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128244 p = 1 := by simpa only [d128245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14417 p hg
    simpa only [d128245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14419 (p : Pattern) (guard : d128246 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128246, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128246, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128245 p = 1 := by simpa only [d128246, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14418 p hg
    simpa only [d128246, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14420 (p : Pattern) (guard : d128247 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128246 p = 1 := by simpa only [d128247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14419 p hg
    simpa only [d128247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14421 (p : Pattern) (guard : d488 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14403 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14422 (p : Pattern) (guard : d489 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14421 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14423 (p : Pattern) (guard : d490 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14422 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14424 (p : Pattern) (guard : d501 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14423 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14425 (p : Pattern) (guard : d639 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d501 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14424 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14426 (p : Pattern) (guard : d640 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d639 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14425 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14427 (p : Pattern) (guard : d641 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d640 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14426 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14428 (p : Pattern) (guard : d642 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d641 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14427 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14429 (p : Pattern) (guard : d643 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d642 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14428 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14430 (p : Pattern) (guard : d653 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d653, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d653, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d643 p = 1 := by simpa only [d653, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14429 p hg
    simpa only [d653, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14431 (p : Pattern) (guard : d654 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d653 p = 1 := by simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14430 p hg
    simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14432 (p : Pattern) (guard : d128248 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128247 p = 1 := by simpa only [d128248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14420 p hg
    simpa only [d128248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d654 p = 1 := by simpa only [d128248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14431 p hg
    simpa only [d128248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14433 (p : Pattern) (guard : d128249 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128248 p = 1 := by simpa only [d128249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14432 p hg
    simpa only [d128249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14434 (p : Pattern) (guard : d128250 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128249 p = 1 := by simpa only [d128250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14433 p hg
    simpa only [d128250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14435 (p : Pattern) (guard : d128251 p = 1) : d48359 p ≤ (1 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128243 p = 1 := by simpa only [d128251, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14369 p hg
    simpa only [d128251, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128250 p = 1 := by simpa only [d128251, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14434 p hg
    simpa only [d128251, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14436 (p : Pattern) (guard : d661 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14437 (p : Pattern) (guard : d662 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d661 p = 1 := by simpa only [d662, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14436 p hg
    simpa only [d662, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d662, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d662, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14438 (p : Pattern) (guard : d16158 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14439 (p : Pattern) (guard : d16159 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16158 p = 1 := by simpa only [d16159, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14438 p hg
    simpa only [d16159, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16159, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d16159, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14440 (p : Pattern) (guard : d16160 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d662 p = 1 := by simpa only [d16160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14437 p hg
    simpa only [d16160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16159 p = 1 := by simpa only [d16160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14439 p hg
    simpa only [d16160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14441 (p : Pattern) (guard : d12860 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14442 (p : Pattern) (guard : d12861 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12860 p = 1 := by simpa only [d12861, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14441 p hg
    simpa only [d12861, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12861, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d12861, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14443 (p : Pattern) (guard : d16161 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12861 p = 1 := by simpa only [d16161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14442 p hg
    simpa only [d16161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12602 p = 1 := by simpa only [d16161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14131 p hg
    simpa only [d16161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14444 (p : Pattern) (guard : d16162 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16160 p = 1 := by simpa only [d16162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14440 p hg
    simpa only [d16162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16161 p = 1 := by simpa only [d16162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14443 p hg
    simpa only [d16162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14445 (p : Pattern) (guard : d16163 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16162 p = 1 := by simpa only [d16163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14444 p hg
    simpa only [d16163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16004 p = 1 := by simpa only [d16163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14133 p hg
    simpa only [d16163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14446 (p : Pattern) (guard : d16164 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16164, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16164, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16163 p = 1 := by simpa only [d16164, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14445 p hg
    simpa only [d16164, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14447 (p : Pattern) (guard : d16165 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16165, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16165, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16164 p = 1 := by simpa only [d16165, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14446 p hg
    simpa only [d16165, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14448 (p : Pattern) (guard : d16166 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12603 p = 1 := by simpa only [d16166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14132 p hg
    simpa only [d16166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d70 p = 1 := by simpa only [d16166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13770 p hg
    simpa only [d16166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14449 (p : Pattern) (guard : d16167 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16004 p = 1 := by simpa only [d16167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14133 p hg
    simpa only [d16167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16166 p = 1 := by simpa only [d16167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14448 p hg
    simpa only [d16167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14450 (p : Pattern) (guard : d16168 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16168, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16168, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16167 p = 1 := by simpa only [d16168, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14449 p hg
    simpa only [d16168, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14451 (p : Pattern) (guard : d16169 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16169, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16169, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16168 p = 1 := by simpa only [d16169, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14450 p hg
    simpa only [d16169, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14452 (p : Pattern) (guard : d16170 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16165 p = 1 := by simpa only [d16170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14447 p hg
    simpa only [d16170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16169 p = 1 := by simpa only [d16170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14451 p hg
    simpa only [d16170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14453 (p : Pattern) (guard : d16171 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16170 p = 1 := by simpa only [d16171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14452 p hg
    simpa only [d16171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16008 p = 1 := by simpa only [d16171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14137 p hg
    simpa only [d16171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14454 (p : Pattern) (guard : d16172 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16171 p = 1 := by simpa only [d16172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14453 p hg
    simpa only [d16172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14455 (p : Pattern) (guard : d16173 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16172 p = 1 := by simpa only [d16173, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14454 p hg
    simpa only [d16173, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16173, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16173, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14456 (p : Pattern) (guard : d16174 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16174, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16174, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16173 p = 1 := by simpa only [d16174, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14455 p hg
    simpa only [d16174, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14457 (p : Pattern) (guard : d673 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d234 p = 1 := by simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13938 p hg
    simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14458 (p : Pattern) (guard : d16175 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16008 p = 1 := by simpa only [d16175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14137 p hg
    simpa only [d16175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d673 p = 1 := by simpa only [d16175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14457 p hg
    simpa only [d16175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14459 (p : Pattern) (guard : d16176 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16175 p = 1 := by simpa only [d16176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14458 p hg
    simpa only [d16176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14460 (p : Pattern) (guard : d16177 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16176 p = 1 := by simpa only [d16177, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14459 p hg
    simpa only [d16177, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16177, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16177, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14461 (p : Pattern) (guard : d16178 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16178, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16178, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16177 p = 1 := by simpa only [d16178, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14460 p hg
    simpa only [d16178, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14462 (p : Pattern) (guard : d16179 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16174 p = 1 := by simpa only [d16179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14456 p hg
    simpa only [d16179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16178 p = 1 := by simpa only [d16179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14461 p hg
    simpa only [d16179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14463 (p : Pattern) (guard : d16180 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16179 p = 1 := by simpa only [d16180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14462 p hg
    simpa only [d16180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14464 (p : Pattern) (guard : d16181 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16180 p = 1 := by simpa only [d16181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14463 p hg
    simpa only [d16181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14465 (p : Pattern) (guard : d16182 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16181 p = 1 := by simpa only [d16182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14464 p hg
    simpa only [d16182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14466 (p : Pattern) (guard : d682 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d673 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14457 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14467 (p : Pattern) (guard : d683 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d682 p = 1 := by simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14466 p hg
    simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14468 (p : Pattern) (guard : d684 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d683 p = 1 := by simpa only [d684, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14467 p hg
    simpa only [d684, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d684, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d684, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14469 (p : Pattern) (guard : d685 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d685, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d685, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d684 p = 1 := by simpa only [d685, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14468 p hg
    simpa only [d685, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14470 (p : Pattern) (guard : d16183 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16178 p = 1 := by simpa only [d16183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14461 p hg
    simpa only [d16183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d685 p = 1 := by simpa only [d16183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14469 p hg
    simpa only [d16183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14471 (p : Pattern) (guard : d16184 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16183 p = 1 := by simpa only [d16184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14470 p hg
    simpa only [d16184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14472 (p : Pattern) (guard : d16185 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16184 p = 1 := by simpa only [d16185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14471 p hg
    simpa only [d16185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14473 (p : Pattern) (guard : d16186 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16185 p = 1 := by simpa only [d16186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14472 p hg
    simpa only [d16186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14474 (p : Pattern) (guard : d16187 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16182 p = 1 := by simpa only [d16187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14465 p hg
    simpa only [d16187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16186 p = 1 := by simpa only [d16187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14473 p hg
    simpa only [d16187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14475 (p : Pattern) (guard : d128252 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16187 p = 1 := by simpa only [d128252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14474 p hg
    simpa only [d128252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14476 (p : Pattern) (guard : d16204 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16178 p = 1 := by simpa only [d16204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14461 p hg
    simpa only [d16204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14477 (p : Pattern) (guard : d16205 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16204 p = 1 := by simpa only [d16205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14476 p hg
    simpa only [d16205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14478 (p : Pattern) (guard : d16206 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16205 p = 1 := by simpa only [d16206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14477 p hg
    simpa only [d16206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14479 (p : Pattern) (guard : d16207 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16206 p = 1 := by simpa only [d16207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14478 p hg
    simpa only [d16207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14480 (p : Pattern) (guard : d16208 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16207 p = 1 := by simpa only [d16208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14479 p hg
    simpa only [d16208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14481 (p : Pattern) (guard : d16209 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16208 p = 1 := by simpa only [d16209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14480 p hg
    simpa only [d16209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14482 (p : Pattern) (guard : d128253 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128252 p = 1 := by simpa only [d128253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14475 p hg
    simpa only [d128253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16209 p = 1 := by simpa only [d128253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14481 p hg
    simpa only [d128253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14483 (p : Pattern) (guard : d128254 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128253 p = 1 := by simpa only [d128254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14482 p hg
    simpa only [d128254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14484 (p : Pattern) (guard : d128255 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128254 p = 1 := by simpa only [d128255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14483 p hg
    simpa only [d128255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14485 (p : Pattern) (guard : d128256 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128256, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128256, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128255 p = 1 := by simpa only [d128256, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14484 p hg
    simpa only [d128256, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14486 (p : Pattern) (guard : d128257 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128256 p = 1 := by simpa only [d128257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14485 p hg
    simpa only [d128257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14487 (p : Pattern) (guard : d727 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d685 p = 1 := by simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14469 p hg
    simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14488 (p : Pattern) (guard : d728 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d727 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14487 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14489 (p : Pattern) (guard : d729 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d728 p = 1 := by simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14488 p hg
    simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14490 (p : Pattern) (guard : d730 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d729 p = 1 := by simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14489 p hg
    simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14491 (p : Pattern) (guard : d731 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d730 p = 1 := by simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14490 p hg
    simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14492 (p : Pattern) (guard : d732 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d731 p = 1 := by simpa only [d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14491 p hg
    simpa only [d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14493 (p : Pattern) (guard : d733 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d732 p = 1 := by simpa only [d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14492 p hg
    simpa only [d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14494 (p : Pattern) (guard : d734 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d733 p = 1 := by simpa only [d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14493 p hg
    simpa only [d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14495 (p : Pattern) (guard : d735 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d734 p = 1 := by simpa only [d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14494 p hg
    simpa only [d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14496 (p : Pattern) (guard : d736 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d736, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d735 p = 1 := by simpa only [d736, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14495 p hg
    simpa only [d736, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14497 (p : Pattern) (guard : d737 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d736 p = 1 := by simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14496 p hg
    simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14498 (p : Pattern) (guard : d128258 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128257 p = 1 := by simpa only [d128258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14486 p hg
    simpa only [d128258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d128258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14497 p hg
    simpa only [d128258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14499 (p : Pattern) (guard : d128259 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128258 p = 1 := by simpa only [d128259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14498 p hg
    simpa only [d128259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128259, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
